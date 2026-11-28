import OMAReductions.R_Erdos402_erdos_402_R2_H2_R1
import Mathlib

-- Step Erdos402.erdos_402.R2.H2.R1.H2: the combinatorial prime criterion of the medium range.
--
-- Own argument; the second prime q of the statement is not needed.
-- Let N = |A| and suppose every pair has a < N * gcd a b, so every cofactor a / gcd a b is
-- at most N - 1.
--  1. p > N divides no element: gcd A = 1 gives an element b not divisible by p, and the
--     cofactor of a against b would be a multiple of p.
--  2. Residues modulo p are pairwise distinct on A, and p | a + b forces
--     a / gcd a b + b / gcd a b = p.
--  3. The residues of A together with the negated residues of the elements without a partner
--     are distinct and nonzero, so at least 2N - p + 1 elements a have a partner b, p | a + b.
--  4. For such a pair write a = u * g, b = v * g with u + v = p. The cofactor u lies in
--     [p - N + 1, N - 1], an interval with only 2N - p - 1 elements.
--  5. Under the double-gap hypothesis the cofactor determines the pair: if u*d, v*d, u*d', v*d'
--     all lie in A then d = d'. Steps 3, 4 and 5 are contradictory.

-- Two coprime divisors s < t of α cannot both be this close when (N - α)^2 < α.
theorem e402c_close_aux (N α s t : ℕ) (hα : α < N) (hgap : (N - α) ^ 2 < α)
    (hle : s * t ≤ α) (hlt : s < t) (h1 : α * t < N * s) : False := by
  obtain ⟨δ, rfl⟩ : ∃ δ, N = α + δ := ⟨N - α, by omega⟩
  rw [Nat.add_sub_cancel_left] at hgap
  have hα0 : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h | h
    · subst h; simp at hgap
    · exact h
  have ht0 : 0 < t := by omega
  have h6 : α * (s + 1) ≤ α * t := Nat.mul_le_mul_left α hlt
  have h7 : δ * (s + 1) ≤ δ * t := Nat.mul_le_mul_left δ hlt
  have hA : α + δ < δ * t := by nlinarith
  have hB : t * t < α + δ := by
    have h3 : α * t * t < (α + δ) * s * t := Nat.mul_lt_mul_of_pos_right h1 ht0
    have h4 : (α + δ) * s * t ≤ (α + δ) * α := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hle
    have h5 : α * (t * t) < α * (α + δ) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left h5
  have hC : (α + δ) * (α + δ) < (δ * t) * (δ * t) := Nat.mul_self_lt_mul_self hA
  have hD : δ * δ ≤ α := by nlinarith
  have hE : δ * δ * (t * t) ≤ α * (t * t) := Nat.mul_le_mul_right _ hD
  have hF : α * (t * t) < α * (α + δ) := Nat.mul_lt_mul_of_pos_left hB hα0
  have hG : α * (α + δ) ≤ (α + δ) * (α + δ) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem e402c_close (N α s t : ℕ) (hα : α < N) (hgap : (N - α) ^ 2 < α)
    (hs : s ∣ α) (ht : t ∣ α) (hco : Nat.Coprime s t)
    (h1 : α * t < N * s) (h2 : α * s < N * t) : s = 1 ∧ t = 1 := by
  have hα0 : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h | h
    · subst h; simp at hgap
    · exact h
  have hle : s * t ≤ α := Nat.le_of_dvd hα0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd hco hs ht)
  have hEq : s = t := by
    rcases Nat.lt_trichotomy s t with h | h | h
    · exact (e402c_close_aux N α s t hα hgap hle h h1).elim
    · exact h
    · exact (e402c_close_aux N α t s hα hgap (by rwa [Nat.mul_comm]) h h2).elim
  subst hEq
  have h1' : s = 1 := (Nat.coprime_self s).mp hco
  exact ⟨h1', h1'⟩

theorem e402c_gcd_dvd (u v x y : ℕ) (huv : Nat.Coprime u v) (hxy : Nat.Coprime x y) :
    Nat.gcd (u * x) (v * y) ∣ Nat.gcd u y * Nat.gcd x v := by
  have h := Nat.gcd_mul_right_dvd_mul_gcd (v * y) u x
  have e1 : Nat.gcd (v * y) u = Nat.gcd u y := by
    rw [Nat.gcd_comm]
    exact Nat.Coprime.gcd_mul_left_cancel_right y huv.symm
  have e2 : Nat.gcd (v * y) x = Nat.gcd x v := by
    rw [Nat.gcd_comm]
    exact Nat.Coprime.gcd_mul_right_cancel_right v hxy.symm
  rw [e1, e2] at h
  rw [Nat.gcd_comm (u * x) (v * y)]
  exact h

-- Two multipliers of the same reduced pair (u, v), written with coprime x, y.
theorem e402c_core (N u v x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxy : Nat.Coprime x y) (huv : Nat.Coprime u v)
    (hu : u < N) (hv : v < N) (gu : (N - u) ^ 2 < u) (gv : (N - v) ^ 2 < v)
    (hN : N < 2 * u ∨ N < 2 * v)
    (c1 : u * x < N * Nat.gcd (u * x) (v * y)) (c2 : v * y < N * Nat.gcd (u * x) (v * y))
    (c3 : v * x < N * Nat.gcd (v * x) (u * y)) (c4 : u * y < N * Nat.gcd (v * x) (u * y)) :
    x = 1 ∧ y = 1 := by
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · subst h; simp at gu
    · exact h
  have hv0 : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h; simp at gv
    · exact h
  have hs0 : 0 < Nat.gcd u y := Nat.gcd_pos_of_pos_left y hu0
  have hs'0 : 0 < Nat.gcd v y := Nat.gcd_pos_of_pos_left y hv0
  have ht0 : 0 < Nat.gcd x v := Nat.gcd_pos_of_pos_left v hx
  have ht'0 : 0 < Nat.gcd x u := Nat.gcd_pos_of_pos_left u hx
  have hG1 : Nat.gcd (u * x) (v * y) ≤ Nat.gcd u y * Nat.gcd x v :=
    Nat.le_of_dvd (Nat.mul_pos hs0 ht0) (e402c_gcd_dvd u v x y huv hxy)
  have hG2 : Nat.gcd (v * x) (u * y) ≤ Nat.gcd v y * Nat.gcd x u :=
    Nat.le_of_dvd (Nat.mul_pos hs'0 ht'0) (e402c_gcd_dvd v u x y huv.symm hxy)
  have hcx : Nat.Coprime (Nat.gcd x v) (Nat.gcd x u) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right x v)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right x u) huv.symm)
  have hxle : Nat.gcd x v * Nat.gcd x u ≤ x :=
    Nat.le_of_dvd hx
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcx (Nat.gcd_dvd_left x v) (Nat.gcd_dvd_left x u))
  have hcy : Nat.Coprime (Nat.gcd u y) (Nat.gcd v y) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left u y)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left v y) huv)
  have hyle : Nat.gcd u y * Nat.gcd v y ≤ y :=
    Nat.le_of_dvd hy
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcy (Nat.gcd_dvd_right u y) (Nat.gcd_dvd_right v y))
  have hco1 : Nat.Coprime (Nat.gcd u y) (Nat.gcd x u) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right u y)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left x u) hxy.symm)
  have hco2 : Nat.Coprime (Nat.gcd v y) (Nat.gcd x v) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right v y)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left x v) hxy.symm)
  have hsu : Nat.gcd u y ∣ u := Nat.gcd_dvd_left u y
  have ht'u : Nat.gcd x u ∣ u := Nat.gcd_dvd_right x u
  have hs'v : Nat.gcd v y ∣ v := Nat.gcd_dvd_left v y
  have htv : Nat.gcd x v ∣ v := Nat.gcd_dvd_right x v
  generalize Nat.gcd (u * x) (v * y) = G1 at c1 c2 hG1
  generalize Nat.gcd (v * x) (u * y) = G2 at c3 c4 hG2
  generalize Nat.gcd u y = s at hG1 hyle hco1 hsu hs0 hcy
  generalize Nat.gcd x u = t' at hG2 hxle hco1 ht'u ht'0 hcx
  generalize Nat.gcd v y = s' at hG2 hyle hco2 hs'v hs'0 hcy
  generalize Nat.gcd x v = t at hG1 hxle hco2 htv ht0 hcx
  have i : u * t' < N * s := by
    have a1 : u * (t * t') ≤ u * x := Nat.mul_le_mul_left u hxle
    have a2 : N * G1 ≤ N * (s * t) := Nat.mul_le_mul_left N hG1
    have a3 : (u * t') * t < (N * s) * t :=
      calc (u * t') * t = u * (t * t') := by ring
        _ ≤ u * x := a1
        _ < N * G1 := c1
        _ ≤ N * (s * t) := a2
        _ = (N * s) * t := by ring
    exact Nat.lt_of_mul_lt_mul_right a3
  have ii' : u * s < N * t' := by
    have a1 : u * (s * s') ≤ u * y := Nat.mul_le_mul_left u hyle
    have a2 : N * G2 ≤ N * (s' * t') := Nat.mul_le_mul_left N hG2
    have a3 : (u * s) * s' < (N * t') * s' :=
      calc (u * s) * s' = u * (s * s') := by ring
        _ ≤ u * y := a1
        _ < N * G2 := c4
        _ ≤ N * (s' * t') := a2
        _ = (N * t') * s' := by ring
    exact Nat.lt_of_mul_lt_mul_right a3
  obtain ⟨hs1, ht'1⟩ := e402c_close N u s t' hu gu hsu ht'u hco1 i ii'
  have i' : v * s' < N * t := by
    have a1 : v * (s * s') ≤ v * y := Nat.mul_le_mul_left v hyle
    have a2 : N * G1 ≤ N * (s * t) := Nat.mul_le_mul_left N hG1
    have a3 : (v * s') * s < (N * t) * s :=
      calc (v * s') * s = v * (s * s') := by ring
        _ ≤ v * y := a1
        _ < N * G1 := c2
        _ ≤ N * (s * t) := a2
        _ = (N * t) * s := by ring
    exact Nat.lt_of_mul_lt_mul_right a3
  have ii : v * t < N * s' := by
    have a1 : v * (t * t') ≤ v * x := Nat.mul_le_mul_left v hxle
    have a2 : N * G2 ≤ N * (s' * t') := Nat.mul_le_mul_left N hG2
    have a3 : (v * t) * t' < (N * s') * t' :=
      calc (v * t) * t' = v * (t * t') := by ring
        _ ≤ v * x := a1
        _ < N * G2 := c3
        _ ≤ N * (s' * t') := a2
        _ = (N * s') * t' := by ring
    exact Nat.lt_of_mul_lt_mul_right a3
  obtain ⟨hs'1, ht1⟩ := e402c_close N v s' t hv gv hs'v htv hco2 ii i'
  subst hs1 ht'1 hs'1 ht1
  have hG1' : G1 ≤ 1 := by simpa using hG1
  have hG2' : G2 ≤ 1 := by simpa using hG2
  have b1 : N * G1 ≤ N * 1 := Nat.mul_le_mul_left N hG1'
  have b2 : N * G2 ≤ N * 1 := Nat.mul_le_mul_left N hG2'
  have hx2 : x < 2 := by
    by_contra h
    have h2 : 2 ≤ x := by omega
    rcases hN with hN | hN
    · have := Nat.mul_le_mul_left u h2
      omega
    · have := Nat.mul_le_mul_left v h2
      omega
  have hy2 : y < 2 := by
    by_contra h
    have h2 : 2 ≤ y := by omega
    rcases hN with hN | hN
    · have := Nat.mul_le_mul_left u h2
      omega
    · have := Nat.mul_le_mul_left v h2
      omega
  exact ⟨by omega, by omega⟩

-- The same with arbitrary multipliers d, d'.
theorem e402c_mult (N u v d d' : ℕ) (hd : 0 < d) (hd' : 0 < d') (huv : Nat.Coprime u v)
    (hu : u < N) (hv : v < N) (gu : (N - u) ^ 2 < u) (gv : (N - v) ^ 2 < v)
    (hN : N < 2 * u ∨ N < 2 * v)
    (c1 : u * d < N * Nat.gcd (u * d) (v * d')) (c2 : v * d' < N * Nat.gcd (u * d) (v * d'))
    (c3 : v * d < N * Nat.gcd (v * d) (u * d')) (c4 : u * d' < N * Nat.gcd (v * d) (u * d')) :
    d = d' := by
  obtain ⟨x, y, hxy, hdx, hdy⟩ := Nat.exists_coprime d d'
  have hg : 0 < Nat.gcd d d' := Nat.gcd_pos_of_pos_left d' hd
  generalize Nat.gcd d d' = g at hdx hdy hg
  subst hdx hdy
  have hx : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hd
    · exact h
  have hy : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · subst h; simp at hd'
    · exact h
  have e1 : Nat.gcd (u * (x * g)) (v * (y * g)) = Nat.gcd (u * x) (v * y) * g := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.gcd_mul_right]
  have e2 : Nat.gcd (v * (x * g)) (u * (y * g)) = Nat.gcd (v * x) (u * y) * g := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.gcd_mul_right]
  rw [e1] at c1 c2
  rw [e2] at c3 c4
  have c1' : u * x < N * Nat.gcd (u * x) (v * y) := by
    have h : (u * x) * g < (N * Nat.gcd (u * x) (v * y)) * g := by
      rw [Nat.mul_assoc, Nat.mul_assoc]; exact c1
    exact Nat.lt_of_mul_lt_mul_right h
  have c2' : v * y < N * Nat.gcd (u * x) (v * y) := by
    have h : (v * y) * g < (N * Nat.gcd (u * x) (v * y)) * g := by
      rw [Nat.mul_assoc, Nat.mul_assoc]; exact c2
    exact Nat.lt_of_mul_lt_mul_right h
  have c3' : v * x < N * Nat.gcd (v * x) (u * y) := by
    have h : (v * x) * g < (N * Nat.gcd (v * x) (u * y)) * g := by
      rw [Nat.mul_assoc, Nat.mul_assoc]; exact c3
    exact Nat.lt_of_mul_lt_mul_right h
  have c4' : u * y < N * Nat.gcd (v * x) (u * y) := by
    have h : (u * y) * g < (N * Nat.gcd (v * x) (u * y)) * g := by
      rw [Nat.mul_assoc, Nat.mul_assoc]; exact c4
    exact Nat.lt_of_mul_lt_mul_right h
  obtain ⟨rfl, rfl⟩ := e402c_core N u v x y hx hy hxy huv hu hv gu gv hN c1' c2' c3' c4'
  rfl

-- A pair of elements, written through its gcd.
theorem e402c_pair (A : Finset ℕ) (h0 : 0 ∉ A)
    (hlt : ∀ a ∈ A, ∀ b ∈ A, a < A.card * a.gcd b) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
    ∃ g u v, 0 < g ∧ a = u * g ∧ b = v * g ∧ Nat.Coprime u v ∧ u < A.card ∧ v < A.card ∧
      Nat.gcd a b = g := by
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
  obtain ⟨u, v, huv, hau, hbv⟩ := Nat.exists_coprime a b
  have h1 := hlt a ha b hb
  have h2 := hlt b hb a ha
  rw [Nat.gcd_comm b a] at h2
  have hg0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha0
  refine ⟨Nat.gcd a b, u, v, hg0, hau, hbv, huv, ?_, ?_, rfl⟩
  · exact Nat.lt_of_mul_lt_mul_right (lt_of_eq_of_lt hau.symm h1)
  · exact Nat.lt_of_mul_lt_mul_right (lt_of_eq_of_lt hbv.symm h2)

-- Step 1: p divides no element.
theorem e402c_notdvd (A : Finset ℕ) (p : ℕ) (h0 : 0 ∉ A) (hg : A.gcd id = 1)
    (hp : p.Prime) (hNp : A.card < p)
    (hlt : ∀ a ∈ A, ∀ b ∈ A, a < A.card * a.gcd b) (a : ℕ) (ha : a ∈ A) : ¬ p ∣ a := by
  intro hpa
  have hex : ∃ b ∈ A, ¬ p ∣ b := by
    by_contra hall
    have hall' : ∀ b ∈ A, p ∣ id b := by
      intro b hb
      by_contra hnb
      exact hall ⟨b, hb, hnb⟩
    have h1 : p ∣ A.gcd id := Finset.dvd_gcd hall'
    rw [hg] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨b, hb, hpb⟩ := hex
  obtain ⟨g, u, v, hg0, hau, hbv, huv, hu, hv, -⟩ := e402c_pair A h0 hlt a b ha hb
  have hpg : ¬ p ∣ g := fun h => hpb (by rw [hbv]; exact Dvd.dvd.mul_left h v)
  rw [hau] at hpa
  have hpu : p ∣ u := (hp.dvd_mul.mp hpa).resolve_right hpg
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, Nat.zero_mul] at hau
      exact absurd (hau ▸ ha) h0
    · exact h
  have := Nat.le_of_dvd hu0 hpu
  omega

-- Step 2a: a pair with p | a + b has cofactors adding up to p.
theorem e402c_sum (A : Finset ℕ) (p : ℕ) (h0 : 0 ∉ A) (hp : p.Prime) (hNp : A.card < p)
    (hlt : ∀ a ∈ A, ∀ b ∈ A, a < A.card * a.gcd b) (hnd : ∀ a ∈ A, ¬ p ∣ a)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hab : p ∣ a + b) :
    ∃ g u v, 0 < g ∧ a = u * g ∧ b = v * g ∧ Nat.Coprime u v ∧ u < A.card ∧ v < A.card ∧
      u + v = p ∧ Nat.gcd a b = g := by
  obtain ⟨g, u, v, hg0, hau, hbv, huv, hu, hv, hgab⟩ := e402c_pair A h0 hlt a b ha hb
  refine ⟨g, u, v, hg0, hau, hbv, huv, hu, hv, ?_, hgab⟩
  have hpg : ¬ p ∣ g := fun h => hnd a ha (by rw [hau]; exact Dvd.dvd.mul_left h u)
  have h1 : p ∣ (u + v) * g := by
    rw [Nat.add_mul, ← hau, ← hbv]; exact hab
  have h2 : p ∣ u + v := (hp.dvd_mul.mp h1).resolve_right hpg
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, Nat.zero_mul] at hau
      exact absurd (hau ▸ ha) h0
    · exact h
  obtain ⟨k, hk⟩ := h2
  have hk1 : k = 1 := by
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    by_contra hne
    have h2k : 2 ≤ k := by omega
    have := Nat.mul_le_mul_left p h2k
    omega
  subst hk1
  omega

-- Step 2b: residues modulo p are distinct.
theorem e402c_inj_le (A : Finset ℕ) (p : ℕ) (h0 : 0 ∉ A) (hp : p.Prime) (hNp : A.card < p)
    (hlt : ∀ a ∈ A, ∀ b ∈ A, a < A.card * a.gcd b) (hnd : ∀ a ∈ A, ¬ p ∣ a)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hba : b ≤ a) (hmod : a % p = b % p) : a = b := by
  obtain ⟨g, u, v, hg0, hau, hbv, huv, hu, hv, -⟩ := e402c_pair A h0 hlt a b ha hb
  have hpg : ¬ p ∣ g := fun h => hnd a ha (by rw [hau]; exact Dvd.dvd.mul_left h u)
  have h1 : p ∣ a - b := (Nat.modEq_iff_dvd' hba).mp hmod.symm
  have h2 : a - b = (u - v) * g := by rw [hau, hbv, Nat.sub_mul]
  rw [h2] at h1
  have h3 : p ∣ u - v := (hp.dvd_mul.mp h1).resolve_right hpg
  have h4 : u - v = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
  have h5 : v ≤ u := by
    rw [hau, hbv] at hba
    exact Nat.le_of_mul_le_mul_right hba hg0
  have h6 : u = v := by omega
  rw [hau, hbv, h6]

theorem e402c_inj (A : Finset ℕ) (p : ℕ) (h0 : 0 ∉ A) (hp : p.Prime) (hNp : A.card < p)
    (hlt : ∀ a ∈ A, ∀ b ∈ A, a < A.card * a.gcd b) (hnd : ∀ a ∈ A, ¬ p ∣ a)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hmod : a % p = b % p) : a = b := by
  rcases le_total b a with h | h
  · exact e402c_inj_le A p h0 hp hNp hlt hnd a b ha hb h hmod
  · exact (e402c_inj_le A p h0 hp hNp hlt hnd b a hb ha h hmod.symm).symm

-- Steps 3, 4 and 5.
theorem e402c_main (A : Finset ℕ) (p : ℕ) (h0 : 0 ∉ A) (hg : A.gcd id = 1)
    (hp : p.Prime) (hNp : A.card < p) (hp2 : p < 2 * A.card)
    (hgap : ∀ α ∈ Finset.Icc ((p + 1) / 2) A.card,
        (A.card - α) ^ 2 < α ∧ p - α ≤ A.card ∧ (A.card - (p - α)) ^ 2 < p - α)
    (hlt : ∀ a ∈ A, ∀ b ∈ A, a < A.card * a.gcd b) : False := by
  classical
  have hnd : ∀ a ∈ A, ¬ p ∣ a := fun a ha => e402c_notdvd A p h0 hg hp hNp hlt a ha
  have hinj : ∀ a ∈ A, ∀ b ∈ A, a % p = b % p → a = b :=
    fun a ha b hb h => e402c_inj A p h0 hp hNp hlt hnd a b ha hb h
  have hmodpos : ∀ a ∈ A, 0 < a % p :=
    fun a ha => Nat.pos_of_ne_zero (fun h => hnd a ha (Nat.dvd_of_mod_eq_zero h))
  have hmodlt : ∀ a : ℕ, a % p < p := fun a => Nat.mod_lt a hp.pos
  obtain ⟨U, hU⟩ : ∃ U : Finset ℕ, U = A.filter (fun a => ¬ ∃ b ∈ A, p ∣ a + b) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Finset ℕ, M = A.filter (fun a => ∃ b ∈ A, p ∣ a + b) := ⟨_, rfl⟩
  have hMU : M.card + U.card = A.card := by
    rw [hM, hU]; exact Finset.card_filter_add_card_filter_not _
  have hUmem : ∀ a ∈ U, a ∈ A ∧ ¬ ∃ b ∈ A, p ∣ a + b := by
    intro a ha; rw [hU] at ha; exact Finset.mem_filter.mp ha
  have hMmem : ∀ a ∈ M, a ∈ A ∧ ∃ b ∈ A, p ∣ a + b := by
    intro a ha; rw [hM] at ha; exact Finset.mem_filter.mp ha
  -- residues of A, and negated residues of the elements without a partner
  have hR : (A.image (fun a => a % p)).card = A.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb h
    have ha' : a ∈ A := ha
    have hb' : b ∈ A := hb
    exact hinj a ha' b hb' h
  have hR' : (U.image (fun a => p - a % p)).card = U.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb h
    have ha' : a ∈ U := ha
    have hb' : b ∈ U := hb
    have h' : p - a % p = p - b % p := h
    have h1 := hmodlt a
    have h2 := hmodlt b
    have h3 : a % p = b % p := by omega
    exact hinj a (hUmem a ha').1 b (hUmem b hb').1 h3
  have hdisj : Disjoint (A.image (fun a => a % p)) (U.image (fun a => p - a % p)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx'
    have hax' : a % p = x := hax
    have hbx' : p - b % p = x := hbx
    apply (hUmem b hb).2
    refine ⟨a, ha, ?_⟩
    have h1 := hmodlt b
    have h2 : b % p + a % p = p := by omega
    exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, h2, Nat.mod_self])
  have hsub : A.image (fun a => a % p) ∪ U.image (fun a => p - a % p) ⊆ Finset.Ico 1 p := by
    intro x hx
    rw [Finset.mem_Ico]
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
      have hax' : a % p = x := hax
      have h1 := hmodpos a ha
      have h2 := hmodlt a
      constructor <;> omega
    · obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx
      have hbx' : p - b % p = x := hbx
      have h1 := hmodpos b (hUmem b hb).1
      have h2 := hmodlt b
      constructor <;> omega
  have hcount : A.card + U.card ≤ p - 1 := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hR, hR', Nat.card_Ico] at h
    exact h
  -- the pairs with p | a + b
  obtain ⟨P, hP⟩ : ∃ P : Finset (ℕ × ℕ),
      P = (A ×ˢ A).filter (fun ab => p ∣ ab.1 + ab.2) := ⟨_, rfl⟩
  have hPmem : ∀ ab : ℕ × ℕ, ab ∈ P ↔ (ab.1 ∈ A ∧ ab.2 ∈ A) ∧ p ∣ ab.1 + ab.2 := by
    intro ab; rw [hP, Finset.mem_filter, Finset.mem_product]
  have hMP : M.card ≤ P.card := by
    apply Finset.card_le_card_of_surjOn Prod.fst
    intro a ha
    have ha' : a ∈ M := ha
    obtain ⟨haA, b, hb, hab⟩ := hMmem a ha'
    have hmem : (a, b) ∈ P := (hPmem (a, b)).mpr ⟨⟨haA, hb⟩, hab⟩
    exact ⟨(a, b), hmem, rfl⟩
  have hdata : ∀ ab ∈ P, ∃ g u v, 0 < g ∧ ab.1 = u * g ∧ ab.2 = v * g ∧ Nat.Coprime u v ∧
      u < A.card ∧ v < A.card ∧ u + v = p ∧ ab.1 / Nat.gcd ab.1 ab.2 = u := by
    intro ab hab
    obtain ⟨⟨ha, hb⟩, hdvd⟩ := (hPmem ab).mp hab
    obtain ⟨g, u, v, hg0, hau, hbv, huv, hu, hv, hsum, hgab⟩ :=
      e402c_sum A p h0 hp hNp hlt hnd ab.1 ab.2 ha hb hdvd
    refine ⟨g, u, v, hg0, hau, hbv, huv, hu, hv, hsum, ?_⟩
    rw [hgab]
    exact Nat.div_eq_of_eq_mul_left hg0 hau
  have hPI : P.card ≤ (Finset.Icc (p - A.card + 1) (A.card - 1)).card := by
    apply Finset.card_le_card_of_injOn (fun ab : ℕ × ℕ => ab.1 / Nat.gcd ab.1 ab.2)
    · intro ab hab
      have hab' : ab ∈ P := hab
      obtain ⟨g, u, v, hg0, hau, hbv, huv, hu, hv, hsum, hq⟩ := hdata ab hab'
      show ab.1 / Nat.gcd ab.1 ab.2 ∈ Finset.Icc (p - A.card + 1) (A.card - 1)
      rw [hq, Finset.mem_Icc]
      omega
    · intro ab hab ab' hab' heq
      have habP : ab ∈ P := hab
      have habP' : ab' ∈ P := hab'
      have hab1 := (hPmem ab).mp habP
      have hab2 := (hPmem ab').mp habP'
      obtain ⟨g, u, v, hg0, hau, hbv, huv, hu, hv, hsum, hq⟩ := hdata ab habP
      obtain ⟨g', u', v', hg0', hau', hbv', huv', hu', hv', hsum', hq'⟩ := hdata ab' habP'
      have heq' : u = u' := by
        have h : ab.1 / Nat.gcd ab.1 ab.2 = ab'.1 / Nat.gcd ab'.1 ab'.2 := heq
        rw [hq, hq'] at h
        exact h
      subst heq'
      have hvv : v = v' := by omega
      subst hvv
      have hgaps : (A.card - u) ^ 2 < u ∧ (A.card - v) ^ 2 < v := by
        rcases le_total v u with hvu | hvu
        · have hmem : u ∈ Finset.Icc ((p + 1) / 2) A.card := by
            rw [Finset.mem_Icc]; omega
          obtain ⟨g1, -, g2⟩ := hgap u hmem
          have hpv : p - u = v := by omega
          rw [hpv] at g2
          exact ⟨g1, g2⟩
        · have hmem : v ∈ Finset.Icc ((p + 1) / 2) A.card := by
            rw [Finset.mem_Icc]; omega
          obtain ⟨g1, -, g2⟩ := hgap v hmem
          have hpu : p - v = u := by omega
          rw [hpu] at g2
          exact ⟨g2, g1⟩
      have c1 := hlt ab.1 hab1.1.1 ab'.2 hab2.1.2
      have c2 := hlt ab'.2 hab2.1.2 ab.1 hab1.1.1
      have c3 := hlt ab.2 hab1.1.2 ab'.1 hab2.1.1
      have c4 := hlt ab'.1 hab2.1.1 ab.2 hab1.1.2
      rw [Nat.gcd_comm] at c2 c4
      rw [hau, hbv'] at c1 c2
      rw [hbv, hau'] at c3 c4
      have hgg : g = g' :=
        e402c_mult A.card u v g g' hg0 hg0' huv hu hv hgaps.1 hgaps.2 (by omega) c1 c2 c3 c4
      apply Prod.ext
      · rw [hau, hau', hgg]
      · rw [hbv, hbv', hgg]
  rw [Nat.card_Icc] at hPI
  omega

theorem OMA.solution : OMA.R_Erdos402_erdos_402_R2_H2_R1.H2 := by
  unfold OMA.R_Erdos402_erdos_402_R2_H2_R1.H2
  intro A h0 hg _ p _ hp hNp hp2 _ _ _ _ _ hgap
  by_contra hcon
  refine e402c_main A p h0 hg hp hNp hp2 hgap ?_
  intro a ha b hb
  by_contra h
  exact hcon ⟨a, ha, b, hb, Nat.le_of_not_lt h⟩
