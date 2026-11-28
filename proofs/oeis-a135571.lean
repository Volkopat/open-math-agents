import OMAStatements.S_oeis_a135571

-- Problem: A135571 (differences of positive triangular numbers in an odd number of ways).
-- T(a) - T(b) = N iff (a-b)(a+b+1) = 2N; representations with b >= 0 correspond to the odd
-- divisors of N (take the odd factor), and b = 0 occurs iff N is triangular. The number of odd
-- divisors is the number of divisors of the odd part m of N, which is odd iff m is a square (the
-- involution d -> m/d), iff N is a square or twice a square. Twice a square is never triangular.
-- Proof of the statement in #25698 (statement by @agchua). Credit for the proof: @bnb9001

namespace OMA_A135571_Proof

open OMA.S_oeis_a135571

open Finset

theorem two_t (k : ℕ) : 2 * T k = k * (k + 1) := by
  unfold T
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

theorem T_mono {a b : ℕ} (h : b ≤ a) : T b ≤ T a :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem key (a b : ℕ) (h : b < a) : 2 * (T a - T b) = (a - b) * (a + b + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
  have h1 := two_t (b + c)
  have h2 := two_t b
  have hle := T_mono (show b ≤ b + c by omega)
  have e : (b + c) * (b + c + 1) = b * (b + 1) + c * (b + c + b + 1) := by ring
  rw [show b + c - b = c by omega]
  omega

theorem rep_iff (a b N : ℕ) (h : b < a) : T a - T b = N ↔ (a - b) * (a + b + 1) = 2 * N := by
  rw [← key a b h]; omega

theorem bound (a b N : ℕ) (h : b < a) (he : (a - b) * (a + b + 1) = 2 * N) : a ≤ 2 * N := by
  have : 1 * (a + b + 1) ≤ (a - b) * (a + b + 1) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem bound2 (a b N : ℕ) (h : b < a) (he : (a - b) * (a + b + 1) = 2 * N) : a ≤ N := by
  obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
  rw [show b + d - b = d by omega] at he
  have hd : 1 ≤ d := by omega
  nlinarith

/-- representations with `b ≥ 0`, in product form -/
def R (N : ℕ) : Finset (ℕ × ℕ) :=
  (range (2 * N + 1) ×ˢ range (2 * N + 1)).filter
    (fun p => p.2 < p.1 ∧ (p.1 - p.2) * (p.1 + p.2 + 1) = 2 * N)

theorem mem_R (N : ℕ) (p : ℕ × ℕ) :
    p ∈ R N ↔ p.2 < p.1 ∧ (p.1 - p.2) * (p.1 + p.2 + 1) = 2 * N := by
  unfold R
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have := bound p.1 p.2 N h.1 h.2
    exact ⟨⟨by omega, by omega⟩, h⟩

theorem coprime_two_of_odd {d : ℕ} (h : d % 2 = 1) : Nat.Coprime d 2 :=
  Nat.Coprime.symm ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega))

/-- the map from representations to odd divisors -/
def φ (p : ℕ × ℕ) : ℕ := if (p.1 - p.2) % 2 = 1 then p.1 - p.2 else p.1 + p.2 + 1

/-- the inverse map -/
def ψ (N o : ℕ) : ℕ × ℕ :=
  if o < 2 * N / o then ((o + 2 * N / o - 1) / 2, (2 * N / o - o - 1) / 2)
  else ((o + 2 * N / o - 1) / 2, (o - 2 * N / o - 1) / 2)

theorem psi_spec (N o q : ℕ) (hq : N = o * q) (hodd : o % 2 = 1) (hN : 0 < N) :
    (ψ N o).2 < (ψ N o).1 ∧ ((ψ N o).1 - (ψ N o).2) * ((ψ N o).1 + (ψ N o).2 + 1) = 2 * N ∧
      φ (ψ N o) = o := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hq; omega)
  have hf : 2 * N / o = 2 * q := by
    rw [hq, show 2 * (o * q) = o * (2 * q) by ring, Nat.mul_div_cancel_left _ (by omega)]
  unfold ψ
  rw [hf]
  by_cases hc : o < 2 * q
  · rw [if_pos hc]
    have h1 : (2 * q - o - 1) / 2 < (o + 2 * q - 1) / 2 := by omega
    have h2 : (o + 2 * q - 1) / 2 - (2 * q - o - 1) / 2 = o := by omega
    have h3 : (o + 2 * q - 1) / 2 + (2 * q - o - 1) / 2 + 1 = 2 * q := by omega
    refine ⟨h1, ?_, ?_⟩
    · rw [h2, h3, hq]; ring
    · unfold φ; rw [h2, if_pos hodd]
  · rw [if_neg hc]
    have hc' : 2 * q < o := by omega
    have h1 : (o - 2 * q - 1) / 2 < (o + 2 * q - 1) / 2 := by omega
    have h2 : (o + 2 * q - 1) / 2 - (o - 2 * q - 1) / 2 = 2 * q := by omega
    have h3 : (o + 2 * q - 1) / 2 + (o - 2 * q - 1) / 2 + 1 = o := by omega
    refine ⟨h1, ?_, ?_⟩
    · rw [h2, h3, hq]; ring
    · unfold φ; rw [h2, if_neg (by omega), h3]

theorem card_R (N : ℕ) (hN : 0 < N) : (R N).card = ((Nat.divisors N).filter Odd).card := by
  apply Finset.card_nbij' φ (ψ N)
  · intro p hp
    rw [mem_coe, mem_R] at hp
    obtain ⟨hlt, he⟩ := hp
    rw [mem_coe, mem_filter, Nat.mem_divisors]
    unfold φ
    split_ifs with hd
    · refine ⟨⟨Nat.Coprime.dvd_of_dvd_mul_left (coprime_two_of_odd hd) ?_, by omega⟩,
        Nat.odd_iff.mpr hd⟩
      exact ⟨p.1 + p.2 + 1, he.symm⟩
    · have ho : (p.1 + p.2 + 1) % 2 = 1 := by omega
      refine ⟨⟨Nat.Coprime.dvd_of_dvd_mul_left (coprime_two_of_odd ho) ?_, by omega⟩,
        Nat.odd_iff.mpr ho⟩
      exact ⟨p.1 - p.2, by rw [← he, mul_comm]⟩
  · intro o ho
    rw [mem_coe, mem_filter, Nat.mem_divisors] at ho
    obtain ⟨⟨⟨q, hq⟩, -⟩, hodd⟩ := ho
    obtain ⟨h1, h2, -⟩ := psi_spec N o q hq (Nat.odd_iff.mp hodd) hN
    rw [mem_coe, mem_R]
    exact ⟨h1, h2⟩
  · intro p hp
    rw [mem_coe, mem_R] at hp
    obtain ⟨hlt, he⟩ := hp
    unfold φ
    split_ifs with hd
    · have hf : 2 * N / (p.1 - p.2) = p.1 + p.2 + 1 :=
        Nat.div_eq_of_eq_mul_left (by omega) (by rw [← he, mul_comm])
      unfold ψ
      rw [hf, if_pos (by omega)]
      ext <;> simp only <;> omega
    · have hf : 2 * N / (p.1 + p.2 + 1) = p.1 - p.2 :=
        Nat.div_eq_of_eq_mul_left (by omega) (by rw [← he])
      unfold ψ
      rw [hf, if_neg (by omega)]
      ext <;> simp only <;> omega
  · intro o ho
    rw [mem_coe, mem_filter, Nat.mem_divisors] at ho
    obtain ⟨⟨⟨q, hq⟩, -⟩, hodd⟩ := ho
    exact (psi_spec N o q hq (Nat.odd_iff.mp hodd) hN).2.2

/-- parity of a finite set under an involution -/
theorem card_mod_two_invol {α : Type*} [DecidableEq α] (f : α → α) :
    ∀ n (s : Finset α), s.card = n → (∀ x ∈ s, f x ∈ s) → (∀ x ∈ s, f (f x) = x) →
      s.card % 2 = (s.filter (fun x => f x = x)).card % 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hmap hinv
    by_cases hex : ∃ x ∈ s, f x ≠ x
    · obtain ⟨x, hx, hfx⟩ := hex
      have hfxs : f x ∈ s.erase x := mem_erase.mpr ⟨hfx, hmap x hx⟩
      set s' := (s.erase x).erase (f x) with hs'
      have hc : s'.card + 2 = s.card := by
        rw [hs', card_erase_of_mem hfxs, card_erase_of_mem hx]
        have : 2 ≤ s.card := by
          have h1 : 0 < (s.erase x).card := card_pos.mpr ⟨_, hfxs⟩
          rw [card_erase_of_mem hx] at h1; omega
        omega
      have hmem : ∀ y, y ∈ s' ↔ y ∈ s ∧ y ≠ x ∧ y ≠ f x := by
        intro y; rw [hs', mem_erase, mem_erase]; tauto
      have hmap' : ∀ y ∈ s', f y ∈ s' := by
        intro y hy
        rw [hmem] at hy ⊢
        obtain ⟨hy1, hy2, hy3⟩ := hy
        refine ⟨hmap y hy1, ?_, ?_⟩
        · intro h; apply hy3; rw [← h, hinv y hy1]
        · intro h; apply hy2; rw [← hinv y hy1, h, hinv x hx]
      have hinv' : ∀ y ∈ s', f (f y) = y := fun y hy => hinv y ((hmem y).mp hy).1
      have ih' := ih s'.card (by omega) s' rfl hmap' hinv'
      have hfilt : s.filter (fun y => f y = y) = s'.filter (fun y => f y = y) := by
        ext y
        simp only [mem_filter]
        rw [hmem]
        constructor
        · rintro ⟨hy, hfy⟩
          refine ⟨⟨hy, ?_, ?_⟩, hfy⟩
          · intro h; rw [h] at hfy; exact hfx hfy
          · intro h; rw [h, hinv x hx] at hfy; exact hfx hfy.symm
        · rintro ⟨⟨hy, -, -⟩, hfy⟩; exact ⟨hy, hfy⟩
      rw [hfilt, ← ih', ← hc]
      omega
    · push Not at hex
      rw [filter_true_of_mem hex]

theorem card_divisors_mod_two (m : ℕ) (hm : 0 < m) :
    (Nat.divisors m).card % 2 = if IsSquare m then 1 else 0 := by
  rw [card_mod_two_invol (fun d => m / d) _ (Nat.divisors m) rfl]
  · split_ifs with hsq
    · obtain ⟨t, rfl⟩ := hsq
      have ht : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · subst h; simp at hm
        · exact h
      have : (Nat.divisors (t * t)).filter (fun d => t * t / d = d) = {t} := by
        ext d
        simp only [mem_filter, Nat.mem_divisors, mem_singleton]
        constructor
        · rintro ⟨⟨hd, -⟩, he⟩
          have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by positivity)
          have : d * d = t * t := by
            conv_rhs => rw [← Nat.div_mul_cancel hd, he]
          exact Nat.mul_self_inj.mp this
        · intro h; rw [h]
          exact ⟨⟨dvd_mul_right t t, by positivity⟩, Nat.mul_div_cancel _ ht⟩
      rw [this, card_singleton]
    · have : (Nat.divisors m).filter (fun d => m / d = d) = ∅ := by
        apply filter_false_of_mem
        intro d hd he
        apply hsq
        refine ⟨d, ?_⟩
        rw [Nat.mem_divisors] at hd
        conv_lhs => rw [← Nat.div_mul_cancel hd.1, he]
      rw [this, card_empty]
  · intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨Nat.div_dvd_of_dvd hd.1, hd.2⟩
  · intro d hd
    rw [Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1 hd.2

theorem two_pow_mul_odd_inj {a b x y : ℕ} (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exfalso
    obtain ⟨c, rfl⟩ : ∃ c, b = a + c + 1 := ⟨b - a - 1, by omega⟩
    have e : 2 ^ (a + c + 1) * y = 2 ^ a * (2 * (2 ^ c * y)) := by ring
    rw [e] at h
    have := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0:ℕ) < 2) a) h
    omega
  · subst hab; exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0:ℕ) < 2) _) h⟩
  · exfalso
    obtain ⟨c, rfl⟩ : ∃ c, a = b + c + 1 := ⟨a - b - 1, by omega⟩
    have e : 2 ^ (b + c + 1) * x = 2 ^ b * (2 * (2 ^ c * x)) := by ring
    rw [e] at h
    have := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0:ℕ) < 2) b) h
    omega

theorem oddDiv_eq (N k m : ℕ) (hm : m % 2 = 1) (hN : N = 2 ^ k * m) :
    (Nat.divisors N).filter Odd = Nat.divisors m := by
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, hN0⟩, hodd⟩
    refine ⟨?_, by omega⟩
    rw [hN] at hd
    exact Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_right k (coprime_two_of_odd (Nat.odd_iff.mp hodd))) hd
  · rintro ⟨hd, hm0⟩
    refine ⟨⟨by rw [hN]; exact Dvd.dvd.mul_left hd _, by
      rw [hN]; positivity⟩, ?_⟩
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr hm) hd

theorem sq_iff (N k m : ℕ) (hm : m % 2 = 1) (hN : N = 2 ^ k * m) :
    IsSquare m ↔ IsSquare N ∨ ∃ s, N = 2 * s ^ 2 := by
  constructor
  · rintro ⟨t, rfl⟩
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left; exact ⟨2 ^ j * t, by rw [hN, pow_add]; ring⟩
    · right; exact ⟨2 ^ j * t, by rw [hN, pow_succ, pow_mul']; ring⟩
  · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · have hs0 : s ≠ 0 := by rintro rfl; rw [hN] at hs; simp at hs; omega
      obtain ⟨j, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hs0
      have hu' := Nat.odd_iff.mp hu
      have e : 2 ^ k * m = 2 ^ (2 * j) * (u * u) := by rw [← hN, hs, two_mul, pow_add]; ring
      have := (two_pow_mul_odd_inj hm (by rw [Nat.mul_mod, hu']) e).2
      exact ⟨u, this⟩
    · have hs0 : s ≠ 0 := by rintro rfl; rw [hN] at hs; simp at hs; omega
      obtain ⟨j, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hs0
      have hu' := Nat.odd_iff.mp hu
      have e : 2 ^ k * m = 2 ^ (2 * j + 1) * (u * u) := by rw [← hN, hs, pow_succ, two_mul, pow_add]; ring
      have := (two_pow_mul_odd_inj hm (by rw [Nat.mul_mod, hu']) e).2
      exact ⟨u, this⟩

theorem not_twice_sq_and_tri (N : ℕ) (hN : 0 < N) (s k : ℕ) (hs : N = 2 * s ^ 2) (hk : N = T k) :
    False := by
  have h := two_t k
  rw [← hk, hs] at h
  -- (2k+1)^2 = (4s)^2 + 1
  have e : (2 * k + 1) * (2 * k + 1) = (4 * s) * (4 * s) + 1 := by nlinarith
  have hlt : 4 * s < 2 * k + 1 := by nlinarith
  have : (4 * s + 1) * (4 * s + 1) ≤ (2 * k + 1) * (2 * k + 1) := Nat.mul_self_le_mul_self hlt
  have hs0 : s = 0 := by nlinarith
  subst hs0; simp at hs; omega

theorem T_inj {a k : ℕ} (h : a * (a + 1) = k * (k + 1)) : a = k := by
  rcases Nat.lt_trichotomy a k with hl | hl | hl
  · exfalso
    have : a * (a + 1) < k * (k + 1) := Nat.mul_lt_mul'' hl (by omega)
    omega
  · exact hl
  · exfalso
    have : k * (k + 1) < a * (a + 1) := Nat.mul_lt_mul'' hl (by omega)
    omega

open Classical in
theorem ways_eq (N : ℕ) (hN : 0 < N) :
    ways N + (if ∃ k, N = T k then 1 else 0) = (R N).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := R N) (p := fun p => 0 < p.2)
  have hw : ways N = ((R N).filter (fun p => 0 < p.2)).card := by
    unfold ways
    congr 1
    ext p
    simp only [mem_filter, mem_product, mem_Icc, mem_R]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, hlt, he⟩
      have hle := T_mono hlt.le
      exact ⟨⟨hlt, (rep_iff _ _ _ hlt).mp (by omega)⟩, by omega⟩
    · rintro ⟨⟨hlt, he⟩, h0⟩
      have hb := bound2 p.1 p.2 N hlt he
      have hT := (rep_iff _ _ _ hlt).mpr he
      have hle := T_mono hlt.le
      exact ⟨⟨⟨by omega, hb⟩, by omega, by omega⟩, hlt, by omega⟩
  have h0 : ((R N).filter (fun p => ¬ 0 < p.2)).card = if ∃ k, N = T k then 1 else 0 := by
    split_ifs with htri
    · obtain ⟨k, hk⟩ := htri
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp [T] at hk; omega
        · exact h
      have : (R N).filter (fun p => ¬ 0 < p.2) = {(k, 0)} := by
        ext p
        simp only [mem_filter, mem_R, mem_singleton]
        constructor
        · rintro ⟨⟨hlt, he⟩, hp⟩
          have hp2 : p.2 = 0 := by omega
          rw [hp2, Nat.sub_zero, add_zero] at he
          have h2 := two_t k
          rw [← hk] at h2
          have := T_inj (he.trans h2)
          ext <;> simp [this, hp2]
        · rintro rfl
          refine ⟨⟨hk0, ?_⟩, by simp⟩
          simp only [Nat.sub_zero, add_zero]
          rw [hk, two_t]
      rw [this, card_singleton]
    · apply card_eq_zero.mpr
      apply filter_false_of_mem
      intro p hp hp2
      rw [mem_R] at hp
      apply htri
      refine ⟨p.1, ?_⟩
      have hp0 : p.2 = 0 := by omega
      have he := hp.2
      rw [hp0, Nat.sub_zero, add_zero] at he
      have h2 := two_t p.1
      omega
  omega

open Classical in
theorem stmt' : ∀ N : ℕ, 0 < N →
    (Odd (ways N) ↔ ((IsSquare N ∨ (∃ m, N = 2 * m ^ 2) ∨ ∃ k, N = T k) ∧
      ¬ (IsSquare N ∧ ∃ k, N = T k))) := by
  intro N hN
  obtain ⟨k, m, hm, hNm⟩ := Nat.exists_eq_two_pow_mul_odd (show N ≠ 0 by omega)
  have hm' := Nat.odd_iff.mp hm
  have hm0 : 0 < m := by omega
  have hw := ways_eq N hN
  rw [card_R N hN, oddDiv_eq N k m hm' hNm] at hw
  have hpar := card_divisors_mod_two m hm0
  have hsq := sq_iff N k m hm' hNm
  have hno := not_twice_sq_and_tri N hN
  rw [Nat.odd_iff]
  by_cases htri : ∃ k, N = T k
  · rw [if_pos htri] at hw
    obtain ⟨kk, hkk⟩ := htri
    by_cases hs : IsSquare m
    · rw [if_pos hs] at hpar
      have hN' : IsSquare N := by
        rcases hsq.mp hs with h | ⟨s, hs'⟩
        · exact h
        · exact (hno s kk hs' hkk).elim
      constructor
      · intro h; omega
      · rintro ⟨-, h⟩; exact (h ⟨hN', kk, hkk⟩).elim
    · rw [if_neg hs] at hpar
      have hN' : ¬ IsSquare N := fun h => hs (hsq.mpr (Or.inl h))
      constructor
      · intro _; exact ⟨Or.inr (Or.inr ⟨kk, hkk⟩), fun h => hN' h.1⟩
      · intro _; omega
  · rw [if_neg htri] at hw
    have e1 : ((IsSquare N ∨ (∃ m, N = 2 * m ^ 2) ∨ ∃ k, N = T k) ∧
        ¬ (IsSquare N ∧ ∃ k, N = T k)) ↔ IsSquare m := by
      rw [hsq]
      constructor
      · rintro ⟨h | h | h, -⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact (htri h).elim
      · intro h; exact ⟨by tauto, fun h' => htri h'.2⟩
    rw [e1]
    split_ifs at hpar with hs
    · constructor
      · intro _; exact hs
      · intro _; omega
    · constructor
      · intro h; omega
      · intro h; exact (hs h).elim

end OMA_A135571_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a135571.main := OMA_A135571_Proof.stmt'
