import OMAStatements.S_oeis_a099500

/-!
# A product twice a square between consecutive positive squares

Granville and Selfridge proved Kaplansky's conjecture by a walk through products
of neighboring integers with a common multiplier. See Theorem 1 and Proposition 1
in their 2001 paper: https://doi.org/10.37236/1549.

In this proof the two walk vertices are a square and twice a square chosen near
the center n+1. Their connecting interval satisfies an integer quadratic bound,
which places each pair of successive products between the two square endpoints.
Removing repeated pairs and square endpoints gives the required set.
-/

namespace KapProof

def nearCenter (n u : ℕ) : Prop :=
  ((u : ℤ) - ((n : ℤ) + 1)) ^ 2 ≤ 2 * (n : ℤ) + 1

private lemma square_endpoint (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : ℕ, 0 < s ∧ nearCenter n (s ^ 2) := by
  let a := (n + 1).sqrt
  have hlo : a ^ 2 ≤ n + 1 := Nat.sqrt_le' _
  have hhi : n + 1 < (a + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have ha : 0 < a := by
    by_contra! h
    have : a = 0 := by omega
    simp [this] at hhi
  have lo : (a : ℤ) ^ 2 ≤ (n : ℤ) + 1 := by exact_mod_cast hlo
  have hi : (n : ℤ) + 1 < ((a : ℤ) + 1) ^ 2 := by exact_mod_cast hhi
  by_cases h : (n : ℤ) + 1 ≤ (a : ℤ) ^ 2 + a
  · refine ⟨a, ha, ?_⟩
    unfold nearCenter
    push_cast
    have bound := sq_le_sq' (a := (a : ℤ)^2 - (n + 1)) (b := (a : ℤ))
      (by linarith) (by linarith)
    linarith
  · refine ⟨a + 1, Nat.succ_pos _, ?_⟩
    unfold nearCenter
    push_cast
    have mid : (a : ℤ)^2 + a + 1 ≤ n + 1 := by omega
    have bound := sq_le_sq' (a := ((a : ℤ) + 1)^2 - (n + 1)) (b := (a : ℤ))
      (by linarith) (by nlinarith)
    linarith

private lemma double_square_endpoint (n : ℕ) (hn : 1 ≤ n) :
    ∃ t : ℕ, 0 < t ∧ nearCenter n (2 * t ^ 2) := by
  let a := ((n + 1) / 2).sqrt
  have hlo : a^2 ≤ (n + 1) / 2 := Nat.sqrt_le' _
  have hhi : (n + 1) / 2 < (a + 1)^2 := Nat.lt_succ_sqrt' _
  have ha : 0 < a := by
    by_contra! h
    have : a = 0 := by omega
    simp [this] at hhi
    omega
  have hlo' : 2 * a^2 ≤ n + 1 := by omega
  have hhi' : n + 1 < 2 * (a + 1)^2 := by omega
  have lo : 2 * (a : ℤ)^2 ≤ (n : ℤ) + 1 := by exact_mod_cast hlo'
  have hi : (n : ℤ) + 1 < 2 * ((a : ℤ) + 1)^2 := by exact_mod_cast hhi'
  have pos : (0 : ℤ) < a := by exact_mod_cast ha
  have near (t : ℕ)
      (h₁ : -(2 * (t : ℤ)) ≤ 2 * (t : ℤ)^2 - n)
      (h₂ : 2 * (t : ℤ)^2 - n ≤ 2 * (t : ℤ)) :
      nearCenter n (2 * t^2) := by
    unfold nearCenter
    push_cast
    nlinarith only [sq_le_sq' h₁ h₂]
  by_cases h : (n : ℤ) ≤ 2 * (a : ℤ)^2 + 2 * a
  · exact ⟨a, ha, near a (by linarith) (by linarith)⟩
  · refine ⟨a + 1, Nat.succ_pos _, near _ ?_ ?_⟩ <;> push_cast <;> nlinarith

lemma endpoints (n : ℕ) (hn : 1 ≤ n) :
    ∃ s t : ℕ, 0 < s ∧ 0 < t ∧ nearCenter n (s^2) ∧ nearCenter n (2*t^2) := by
  obtain ⟨s, hs, hnear₁⟩ := square_endpoint n hn
  obtain ⟨t, ht, hnear₂⟩ := double_square_endpoint n hn
  exact ⟨s, t, hs, ht, hnear₁, hnear₂⟩

end KapProof

namespace KapProof

lemma nearCenter_between {n a b k : ℕ} (ha : nearCenter n a) (hb : nearCenter n b)
    (hak : a ≤ k) (hkb : k ≤ b) : nearCenter n k := by
  unfold nearCenter at *
  have h₁ : (a : ℤ) ≤ k := by exact_mod_cast hak
  have h₂ : (k : ℤ) ≤ b := by exact_mod_cast hkb
  by_cases hk : (k : ℤ) ≤ (n : ℤ) + 1
  · nlinarith only [ha, mul_nonneg (sub_nonneg.mpr h₁)
      (show 0 ≤ 2 * ((n : ℤ) + 1) - a - k by omega)]
  · nlinarith only [hb, mul_nonneg (sub_nonneg.mpr h₂)
      (show 0 ≤ (b : ℤ) + k - 2 * ((n : ℤ) + 1) by omega)]

/-- A common multiplier brings consecutive walk vertices into the closed interval. -/
lemma walk_hop (n a : ℕ) (hn : 1 ≤ n) (ha : 0 < a) (hnear : nearCenter n a) :
    ∃ w : ℕ, 0 < w ∧ n^2 ≤ a*w ∧ (a+1)*w ≤ (n+1)^2 := by
  let q := (n^2-1)/a
  have hn' : 0 < n^2 := pow_pos hn 2
  have hpred : n^2-1+1 = n^2 := by omega
  have hlow : n^2-1 < a*(q+1) := Nat.lt_mul_div_succ _ ha
  have hhigh : a*q ≤ n^2-1 := Nat.mul_div_le _ _
  have hcurve : a^2 + n^2 ≤ (2*n+2)*a := by
    unfold nearCenter at hnear
    zify
    nlinarith only [hnear]
  have hsum : a + (q+1) ≤ 2*n+2 := by
    by_contra! h
    have hl : 2*n+2 ≤ a+q := by omega
    have hm := Nat.mul_le_mul_right a hl
    nlinarith only [hcurve, hm, hhigh, hpred]
  refine ⟨q+1, Nat.succ_pos q, by omega, ?_⟩
  calc
    (a+1)*(q+1) = a*q+(a+(q+1)) := by ring
    _ ≤ (n^2-1)+(2*n+2) := Nat.add_le_add hhigh hsum
    _ = (n+1)^2 := by nlinarith only [hpred]

/-- The product along the walk agrees with the ratio of its endpoints up to a square. -/
lemma walk_up (n a b : ℕ) (hn : 1 ≤ n) (ha : 0 < a) (hab : a ≤ b)
    (hA : nearCenter n a) (hB : nearCenter n b) :
    ∃ L : List ℕ, (∀ x ∈ L, n^2 ≤ x ∧ x ≤ (n+1)^2) ∧
      ∃ q : ℕ, 0 < q ∧ L.prod * a = b * q^2 := by
  have walk : ∀ k : ℕ, a ≤ k → k ≤ b →
      ∃ L : List ℕ, (∀ x ∈ L, n^2 ≤ x ∧ x ≤ (n+1)^2) ∧
        ∃ q : ℕ, 0 < q ∧ L.prod * a = k * q^2 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _
      exact ⟨[], by simp, 1, by decide, by simp⟩
    | succ k hk ih =>
      intro hkb
      have hkpos : 0 < k := by omega
      obtain ⟨L, hL, q, hq, he⟩ := ih (by omega)
      obtain ⟨w, hw, hwlo, hwhi⟩ := walk_hop n k hn hkpos
        (nearCenter_between hA hB hk (by omega))
      have hmono : k*w ≤ (k+1)*w := Nat.mul_le_mul_right w (by omega)
      refine ⟨k*w :: (k+1)*w :: L, ?_, k*w*q, by positivity, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hwlo, hmono.trans hwhi⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hwlo.trans hmono, hwhi⟩
          · exact hL x hx
      · simp only [List.prod_cons]
        calc
          k*w*((k+1)*w*L.prod)*a = (k+1)*k*w^2*(L.prod*a) := by ring
          _ = (k+1)*(k*w*q)^2 := by rw [he]; ring
  exact walk b hab le_rfl

end KapProof

namespace KapProof

/-- Discard square endpoints and retain the interior entries of odd multiplicity. -/
lemma strip_walk (n : ℕ) (hn : 1 ≤ n) (L : List ℕ)
    (hL : ∀ x ∈ L, n ^ 2 ≤ x ∧ x ≤ (n + 1) ^ 2) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc (n ^ 2 + 1) ((n + 1) ^ 2 - 1) ∧
      ∃ q : ℕ, 0 < q ∧ L.prod = (∏ x ∈ S, x) * q ^ 2 := by
  induction L with
  | nil => exact ⟨∅, Finset.empty_subset _, 1, by decide, by simp⟩
  | cons x L ih =>
    have hx := hL x (by simp)
    obtain ⟨S, hS, q, hq, hprod⟩ :=
      ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    simp only [List.prod_cons, hprod]
    by_cases hleft : x = n ^ 2
    · refine ⟨S, hS, n * q, Nat.mul_pos hn hq, ?_⟩
      rw [hleft]
      ring
    by_cases hright : x = (n + 1) ^ 2
    · refine ⟨S, hS, (n + 1) * q, Nat.mul_pos (Nat.succ_pos _) hq, ?_⟩
      rw [hright]
      ring
    have hinside : x ∈ Finset.Icc (n ^ 2 + 1) ((n + 1) ^ 2 - 1) :=
      Finset.mem_Icc.mpr (by omega)
    by_cases hmem : x ∈ S
    · have hxpos : 0 < x := lt_of_lt_of_le (pow_pos hn 2) hx.1
      refine ⟨S.erase x, (Finset.erase_subset x S).trans hS, x * q, Nat.mul_pos hxpos hq, ?_⟩
      rw [← S.mul_prod_erase (fun z : ℕ => z) hmem]
      ring
    · refine ⟨insert x S, Finset.insert_subset hinside hS, q, hq, ?_⟩
      rw [Finset.prod_insert hmem]
      ring

/-- A positive square factor can be cancelled from a representation as twice a square. -/
lemma cancel_twice_square (p d v : ℕ) (hd : 0 < d) (h : p * d ^ 2 = 2 * v ^ 2) :
    ∃ m : ℕ, p = 2 * m ^ 2 := by
  have hsq : (2 * v) ^ 2 = d ^ 2 * (2 * p) := by
    calc
      (2 * v) ^ 2 = 2 * (2 * v ^ 2) := by ring
      _ = _ := by rw [← h]; ring
  have hdvd : d ∣ 2 * v :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 2) (by decide)).mp ⟨_, hsq⟩
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, mul_pow] at hsq
  have hk2 : k ^ 2 = 2 * p := Nat.eq_of_mul_eq_mul_left (pow_pos hd _) hsq
  have heven : 2 ∣ k := Nat.prime_two.dvd_of_dvd_pow ⟨p, hk2⟩
  obtain ⟨m, hm⟩ := heven
  refine ⟨m, ?_⟩
  rw [hm] at hk2
  nlinarith

lemma reduce_walk (n : ℕ) (hn : 1 ≤ n) (L : List ℕ)
    (hL : ∀ x ∈ L, n ^ 2 ≤ x ∧ x ≤ (n + 1) ^ 2)
    (u v : ℕ) (hu : 0 < u) (he : L.prod * u ^ 2 = 2 * v ^ 2) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc (n ^ 2 + 1) ((n + 1) ^ 2 - 1) ∧
      ∃ m : ℕ, (∏ x ∈ S, x) = 2 * m ^ 2 := by
  obtain ⟨S, hS, q, hq, hprod⟩ := strip_walk n hn L hL
  refine ⟨S, hS, cancel_twice_square _ (q * u) v (Nat.mul_pos hq hu) ?_⟩
  rwa [mul_pow, ← mul_assoc, ← hprod]

end KapProof

open KapProof

theorem OMA.solution : type_of% @OMA.S_oeis_a099500.main := by
  intro n hn
  obtain ⟨s,t,hs,ht,hS,hT⟩ := endpoints n hn
  by_cases h : s^2 ≤ 2*t^2
  · obtain ⟨L,hL,q,hq,he⟩ := walk_up n (s^2) (2*t^2) hn (by positivity) h hS hT
    apply reduce_walk n hn L hL s (t*q) hs
    rw [he]
    ring
  · obtain ⟨L,hL,q,hq,he⟩ := walk_up n (2*t^2) (s^2) hn (by positivity) (by omega) hT hS
    apply reduce_walk n hn L hL (2*t) (s*q) (by positivity)
    calc
      L.prod*(2*t)^2 = 2*(L.prod*(2*t^2)) := by ring
      _ = 2*(s*q)^2 := by rw [he]; ring
