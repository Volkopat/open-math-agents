import OMAStatements.S_oeis_a308222

-- Problem: A308222: Numbers that are the perimeter of a primitive Heronian isosceles triangle.
-- Upstream: formal-conjectures statements/oeis-a308222.lean:0 (declaration OMA.S_oeis_a308222.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let Q be the set of odd squares and of the numbers 2t^2 with t >= 1. By the
-- classification of primitive Pythagorean triples (x = m^2 - n^2, y = 2mn, z = m^2 + n^2), the
-- differences z - x, z - y are 2n^2 and (m - n)^2, so IsDiff is Q (conversely explicit triples).
-- For a triangle a, a, b Heron's formula forces b = 2u even and u^2 + h^2 = a^2 with gcd(u, h) = 1,
-- so the perimeter is 2(a + u) with a + u = 2m^2 or (m + n)^2, at least 3: the perimeters are the
-- numbers 2d with d in Q, d >= 3 (conversely explicit triangles). Q starts with 1, 2, so counting
-- gives count IsPerim (2y) + 2 = count IsDiff y for y >= 3, and Nat.nth shifts the index by 2.

namespace N12A308222

open OMA.S_oeis_a308222

/-- The odd squares and the numbers 2t^2 with t >= 1. -/
def Q (d : ℕ) : Prop := (∃ s : ℕ, d = (2 * s + 1) ^ 2) ∨ (∃ t : ℕ, 1 ≤ t ∧ d = 2 * t ^ 2)

theorem natAbs_odd (w : ℤ) (h : w % 2 = 1) : w.natAbs % 2 = 1 := by
  rcases Int.natAbs_eq w with h1 | h1 <;> omega

theorem diff_to_Q (d : ℕ) (hd : IsDiff d) : Q d := by
  obtain ⟨x, y, z, -, hy, hxyz, hg, rfl⟩ := hd
  have hxz : x < z := by
    by_contra hc
    have h1 := Nat.pow_le_pow_left (show z ≤ x by omega) 2
    have h2 : 0 < y ^ 2 := pow_pos hy 2
    omega
  have hP : PythagoreanTriple (x : ℤ) (y : ℤ) (z : ℤ) := by
    unfold PythagoreanTriple
    have h1 : ((x ^ 2 + y ^ 2 : ℕ) : ℤ) = ((z ^ 2 : ℕ) : ℤ) := by rw [hxyz]
    push_cast at h1
    linear_combination h1
  have hgZ : Int.gcd (x : ℤ) (y : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hg
  have hz0 : (0 : ℤ) < z := by omega
  have hdZ : ((z - x : ℕ) : ℤ) = (z : ℤ) - (x : ℤ) := Nat.cast_sub hxz.le
  unfold Q
  rcases hP.even_odd_of_coprime hgZ with ⟨_, hyo⟩ | ⟨hxo, _⟩
  · obtain ⟨m, n, -, hx', hz', -, hpar, -⟩ := PythagoreanTriple.coprime_classification' hP.symm
      (by rw [Int.gcd_comm]; exact hgZ) hyo hz0
    left
    have hmn : (m - n) % 2 = 1 := by
      rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have hw := natAbs_odd (m - n) hmn
    refine ⟨(m - n).natAbs / 2, ?_⟩
    have hsq : (((m - n).natAbs : ℕ) : ℤ) ^ 2 = (m - n) ^ 2 := Int.natAbs_pow_two (m - n)
    have hkey : ((z - x : ℕ) : ℤ) = (((m - n).natAbs ^ 2 : ℕ) : ℤ) := by
      rw [hdZ, Nat.cast_pow, hsq, hz', hx']
      ring
    have h2 : z - x = (m - n).natAbs ^ 2 := by exact_mod_cast hkey
    rw [h2]
    congr 1
    omega
  · obtain ⟨m, n, hx', hy', hz', -, -, -⟩ := PythagoreanTriple.coprime_classification' hP hgZ hxo hz0
    right
    refine ⟨n.natAbs, ?_, ?_⟩
    · have hn : n ≠ 0 := by
        rintro rfl
        have h0 : (y : ℤ) = 0 := by
          rw [hy']
          ring
        omega
      have := Int.natAbs_pos.mpr hn
      omega
    · have hsq : ((n.natAbs : ℕ) : ℤ) ^ 2 = n ^ 2 := Int.natAbs_pow_two n
      have hkey : ((z - x : ℕ) : ℤ) = 2 * ((n.natAbs ^ 2 : ℕ) : ℤ) := by
        rw [hdZ, Nat.cast_pow, hsq, hz', hx']
        ring
      exact_mod_cast hkey

theorem Q_to_diff (d : ℕ) (h : Q d) : IsDiff d := by
  unfold IsDiff
  rcases h with ⟨s, rfl⟩ | ⟨t, ht, rfl⟩
  · refine ⟨4 * (s + 1), 4 * s ^ 2 + 8 * s + 3, 4 * s ^ 2 + 8 * s + 5, by positivity,
      by positivity, by ring, ?_, ?_⟩
    · apply Nat.isCoprime_iff_coprime.mp
      refine ⟨(s : ℤ) + 1, -1, ?_⟩
      push_cast
      ring
    · have e : (2 * s + 1) ^ 2 = 4 * s ^ 2 + 4 * s + 1 := by ring
      omega
  · refine ⟨2 * t + 1, 2 * t ^ 2 + 2 * t, 2 * t ^ 2 + 2 * t + 1, by omega, by omega, by ring, ?_,
      by omega⟩
    apply Nat.isCoprime_iff_coprime.mp
    refine ⟨2 * (t : ℤ) + 1, -2, ?_⟩
    push_cast
    ring

theorem perim_iff (p : ℕ) : IsPerim p ↔ ∃ d, Q d ∧ 3 ≤ d ∧ p = 2 * d := by
  constructor
  · rintro ⟨a, b, K, hb, hba, hg, hK, rfl⟩
    have hbe : b % 2 = 0 := by
      by_contra hodd
      obtain ⟨c, rfl⟩ : ∃ c, b = 2 * c + 1 := ⟨b / 2, by omega⟩
      have hle : (2 * c + 1) ^ 2 ≤ 4 * a ^ 2 := by
        have h1 := Nat.pow_le_pow_left hba.le 2
        have e : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
        omega
      obtain ⟨W, hW⟩ : ∃ W, W = 4 * a ^ 2 - (2 * c + 1) ^ 2 := ⟨_, rfl⟩
      have h1 : W + (4 * c ^ 2 + 4 * c + 1) = 4 * a ^ 2 := by
        have e : (2 * c + 1) ^ 2 = 4 * c ^ 2 + 4 * c + 1 := by ring
        omega
      have h2 : 16 * K ^ 2 = 4 * ((c ^ 2 + c) * W) + W := by
        rw [hK, ← hW]
        ring
      obtain ⟨P, hP⟩ : ∃ P, P = (c ^ 2 + c) * W := ⟨_, rfl⟩
      rw [← hP] at h2
      omega
    obtain ⟨u, rfl⟩ : ∃ u, b = 2 * u := ⟨b / 2, by omega⟩
    have hu : 0 < u := by omega
    have hua : u < a := by omega
    have hle : u ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hua.le 2
    obtain ⟨V, hV⟩ : ∃ V, V = a ^ 2 - u ^ 2 := ⟨_, rfl⟩
    have hV' : V + u ^ 2 = a ^ 2 := by omega
    have hK2 : K ^ 2 = u ^ 2 * V := by
      have e1 : (2 * u) ^ 2 = 4 * u ^ 2 := by ring
      have e2 : 4 * a ^ 2 - (2 * u) ^ 2 = 4 * V := by
        rw [e1]
        omega
      rw [e2, e1] at hK
      have h16 : 16 * K ^ 2 = 16 * (u ^ 2 * V) := by
        rw [hK]
        ring
      omega
    have hdvd : u ∣ K := by
      have h1 : u ^ 2 ∣ K ^ 2 := ⟨V, hK2⟩
      exact (Nat.pow_dvd_pow_iff (by norm_num)).mp h1
    obtain ⟨h, rfl⟩ := hdvd
    have hh2 : h ^ 2 = V := by
      have e : (u * h) ^ 2 = u ^ 2 * h ^ 2 := by ring
      rw [e] at hK2
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hu 2) hK2
    have hpy : u ^ 2 + h ^ 2 = a ^ 2 := by omega
    have hlt : u ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hua (by norm_num)
    have hh : 0 < h := by
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · rw [h0] at hpy
        have e : u ^ 2 + 0 ^ 2 = u ^ 2 := by ring
        omega
      · exact h0
    have hga : Nat.Coprime a (2 * u) := hg
    have hua' : Nat.Coprime u a := (Nat.Coprime.coprime_dvd_right (dvd_mul_left u 2) hga).symm
    have huh : Nat.gcd u h = 1 := by
      have g1 := Nat.gcd_dvd_left u h
      have g2 := Nat.gcd_dvd_right u h
      have g3 : Nat.gcd u h ∣ a ^ 2 := by
        rw [← hpy]
        exact dvd_add (dvd_pow g1 (by norm_num)) (dvd_pow g2 (by norm_num))
      have g4 : Nat.gcd u h ∣ Nat.gcd u (a ^ 2) := Nat.dvd_gcd g1 g3
      have g5 : Nat.gcd u (a ^ 2) = 1 := Nat.Coprime.pow_right 2 hua'
      rw [g5] at g4
      exact Nat.dvd_one.mp g4
    have hP : PythagoreanTriple (u : ℤ) (h : ℤ) (a : ℤ) := by
      unfold PythagoreanTriple
      have h1 : ((u ^ 2 + h ^ 2 : ℕ) : ℤ) = ((a ^ 2 : ℕ) : ℤ) := by rw [hpy]
      push_cast at h1
      linear_combination h1
    have hgZ : Int.gcd (u : ℤ) (h : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact huh
    have ha0 : (0 : ℤ) < a := by omega
    refine ⟨a + u, ?_, by omega, by ring⟩
    unfold Q
    rcases hP.even_odd_of_coprime hgZ with ⟨_, hho⟩ | ⟨huo, _⟩
    · obtain ⟨m, n, -, hu', ha', -, hpar, -⟩ := PythagoreanTriple.coprime_classification' hP.symm
        (by rw [Int.gcd_comm]; exact hgZ) hho ha0
      left
      have hmn : (m + n) % 2 = 1 := by
        rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      have hw := natAbs_odd (m + n) hmn
      refine ⟨(m + n).natAbs / 2, ?_⟩
      have hsq : (((m + n).natAbs : ℕ) : ℤ) ^ 2 = (m + n) ^ 2 := Int.natAbs_pow_two (m + n)
      have hkey : ((a + u : ℕ) : ℤ) = (((m + n).natAbs ^ 2 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_pow, hsq, ha', hu']
        ring
      have h2 : a + u = (m + n).natAbs ^ 2 := by exact_mod_cast hkey
      rw [h2]
      congr 1
      omega
    · obtain ⟨m, n, hu', -, ha', -, -, -⟩ := PythagoreanTriple.coprime_classification' hP hgZ huo ha0
      right
      have hsq : ((m.natAbs : ℕ) : ℤ) ^ 2 = m ^ 2 := Int.natAbs_pow_two m
      have hkey : ((a + u : ℕ) : ℤ) = 2 * ((m.natAbs ^ 2 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_pow, hsq, ha', hu']
        ring
      have h2 : a + u = 2 * m.natAbs ^ 2 := by exact_mod_cast hkey
      refine ⟨m.natAbs, ?_, h2⟩
      have hpos : 0 < m.natAbs ^ 2 := by omega
      rcases Nat.eq_zero_or_pos m.natAbs with h0 | h0
      · rw [h0] at hpos
        norm_num at hpos
      · exact h0
  · rintro ⟨d, hQ, h3, rfl⟩
    unfold IsPerim
    rcases hQ with ⟨s, rfl⟩ | ⟨t, ht, rfl⟩
    · have hs : 1 ≤ s := by
        by_contra hc
        have hs0 : s = 0 := by omega
        subst hs0
        norm_num at h3
      obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
      refine ⟨4 * r ^ 2 + 8 * r + 5, 8 * r + 8, 4 * (r + 1) * (4 * r ^ 2 + 8 * r + 3), by omega,
        by omega, ?_, ?_, by ring⟩
      · apply Nat.isCoprime_iff_coprime.mp
        refine ⟨4 * (r : ℤ) ^ 2 + 8 * r + 5, -(2 * ((r : ℤ) + 1) ^ 3 + ((r : ℤ) + 1)), ?_⟩
        push_cast
        ring
      · have e : 4 * (4 * r ^ 2 + 8 * r + 5) ^ 2 =
            (8 * r + 8) ^ 2 + 4 * (4 * r ^ 2 + 8 * r + 3) ^ 2 := by ring
        rw [show 4 * (4 * r ^ 2 + 8 * r + 5) ^ 2 - (8 * r + 8) ^ 2 =
          4 * (4 * r ^ 2 + 8 * r + 3) ^ 2 by omega]
        ring
    · have ht2 : 2 ≤ t := by
        by_contra hc
        have ht1 : t = 1 := by omega
        subst ht1
        norm_num at h3
      obtain ⟨r, rfl⟩ : ∃ r, t = r + 2 := ⟨t - 2, by omega⟩
      refine ⟨2 * r ^ 2 + 6 * r + 5, 4 * r + 6, 2 * (2 * r + 3) * (r + 1) * (r + 2), by omega,
        by omega, ?_, ?_, by ring⟩
      · apply Nat.isCoprime_iff_coprime.mp
        refine ⟨-4 * (r : ℤ) ^ 2 - 12 * r - 7, ((r : ℤ) ^ 2 + 3 * r + 2) * (2 * r + 3), ?_⟩
        push_cast
        ring
      · have e : 4 * (2 * r ^ 2 + 6 * r + 5) ^ 2 =
            (4 * r + 6) ^ 2 + 4 * (2 * (r + 1) * (r + 2)) ^ 2 := by ring
        rw [show 4 * (2 * r ^ 2 + 6 * r + 5) ^ 2 - (4 * r + 6) ^ 2 =
          4 * (2 * (r + 1) * (r + 2)) ^ 2 by omega]
        ring

end N12A308222

open OMA.S_oeis_a308222 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308222.main := by
  classical
  intro n hn
  have hD0 : ¬ IsDiff 0 := by
    intro hd
    rcases N12A308222.diff_to_Q 0 hd with ⟨s, hs⟩ | ⟨t, ht, hts⟩
    · have : 0 < (2 * s + 1) ^ 2 := by positivity
      omega
    · have : 0 < t ^ 2 := pow_pos (by omega) 2
      omega
  have hD1 : IsDiff 1 := N12A308222.Q_to_diff 1 (Or.inl ⟨0, by norm_num⟩)
  have hD2 : IsDiff 2 := N12A308222.Q_to_diff 2 (Or.inr ⟨1, le_refl 1, by norm_num⟩)
  have hP_lt : ∀ x, x < 6 → ¬ IsPerim x := by
    intro x hx hp
    obtain ⟨d, _, h3, h⟩ := (N12A308222.perim_iff x).mp hp
    omega
  have hP_odd : ∀ y, ¬ IsPerim (2 * y + 1) := by
    intro y hp
    obtain ⟨d, _, _, h⟩ := (N12A308222.perim_iff _).mp hp
    omega
  have hP_even : ∀ y, 3 ≤ y → (IsPerim (2 * y) ↔ IsDiff y) := by
    intro y hy
    constructor
    · intro hp
      obtain ⟨d, hq, _, h⟩ := (N12A308222.perim_iff _).mp hp
      have hdy : d = y := by omega
      rw [← hdy]
      exact N12A308222.Q_to_diff d hq
    · intro hd
      exact (N12A308222.perim_iff _).mpr ⟨y, N12A308222.diff_to_Q y hd, hy, rfl⟩
  have hinf : (Set.ofPred IsDiff).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro N
    exact ⟨2 * (N + 1) ^ 2, N12A308222.Q_to_diff _ (Or.inr ⟨N + 1, by omega, rfl⟩),
      by nlinarith [sq_nonneg N]⟩
  have c1 : Nat.count IsDiff 1 = Nat.count IsDiff 0 + (if IsDiff 0 then 1 else 0) :=
    Nat.count_succ IsDiff 0
  have c2 : Nat.count IsDiff 2 = Nat.count IsDiff 1 + (if IsDiff 1 then 1 else 0) :=
    Nat.count_succ IsDiff 1
  have c3 : Nat.count IsDiff 3 = Nat.count IsDiff 2 + (if IsDiff 2 then 1 else 0) :=
    Nat.count_succ IsDiff 2
  rw [if_neg hD0, Nat.count_zero] at c1
  rw [if_pos hD1] at c2
  rw [if_pos hD2] at c3
  have hc3 : Nat.count IsDiff 3 = 2 := by omega
  have hcP0 : ∀ x, x ≤ 6 → Nat.count IsPerim x = 0 := by
    intro x hx
    induction x with
    | zero => exact Nat.count_zero IsPerim
    | succ k ih =>
      rw [Nat.count_succ IsPerim k, ih (by omega), if_neg (hP_lt k (by omega))]
  have claim : ∀ y, 3 ≤ y → Nat.count IsPerim (2 * y) + 2 = Nat.count IsDiff y := by
    intro y hy
    induction y, hy using Nat.le_induction with
    | base => rw [hcP0 (2 * 3) (by norm_num), hc3]
    | succ y hy ih =>
      have e1 : Nat.count IsPerim (2 * (y + 1)) = Nat.count IsPerim (2 * y) +
          (if IsPerim (2 * y) then 1 else 0) + (if IsPerim (2 * y + 1) then 1 else 0) := by
        rw [show 2 * (y + 1) = 2 * y + 1 + 1 by ring, Nat.count_succ IsPerim (2 * y + 1),
          Nat.count_succ IsPerim (2 * y)]
      have e2 := Nat.count_succ IsDiff y
      rw [if_neg (hP_odd y)] at e1
      by_cases hd : IsDiff y
      · rw [if_pos ((hP_even y hy).mpr hd)] at e1
        rw [if_pos hd] at e2
        omega
      · rw [if_neg (fun hp => hd ((hP_even y hy).mp hp))] at e1
        rw [if_neg hd] at e2
        omega
  unfold a a096033
  rw [show n + 2 - 1 = n + 1 by omega]
  obtain ⟨y, hy⟩ : ∃ y, y = Nat.nth IsDiff (n + 1) := ⟨_, rfl⟩
  rw [← hy]
  have hDy : IsDiff y := by
    rw [hy]
    exact Nat.nth_mem_of_infinite hinf (n + 1)
  have hcy : Nat.count IsDiff y = n + 1 := by
    rw [hy]
    exact Nat.count_nth_of_infinite hinf (n + 1)
  have hy3 : 3 ≤ y := by
    by_contra hc
    have hmono := Nat.count_monotone IsDiff (show y ≤ 2 by omega)
    omega
  have hPy : IsPerim (2 * y) := (hP_even y hy3).mpr hDy
  have hcP : Nat.count IsPerim (2 * y) = n - 1 := by
    have := claim y hy3
    omega
  rw [← hcP]
  exact Nat.nth_count hPy
