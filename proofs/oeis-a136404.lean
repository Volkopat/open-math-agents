import OMAStatements.S_oeis_a136404

-- Problem: A136404: Square numbers with more divisors than any smaller square number.
-- Upstream: formal-conjectures statements/oeis-a136404.lean:0 (declaration OMA.S_oeis_a136404.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for n >= 1 the pairs x <= y with 1/n = 1/x + 1/y are (n + d, n + n^2/d) for the
-- divisors d <= n of n^2, and d -> n^2/d maps the divisors <= n onto the divisors >= n, so
-- 2 * A018892(n) = tau(n^2) + 1. Hence A018892(k) < A018892(m) iff tau(k^2) < tau(m^2), and the
-- record condition of A126098 at m is the condition of A136404 at m^2.

/-- 1/n = 1/x + 1/y over the rationals means x*y = n*(x+y), for positive n, x, y. -/
theorem k136404_eq {n x y : ℕ} (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
    ((1 : ℚ) / n = 1 / x + 1 / y) ↔ x * y = n * (x + y) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  rw [div_add_div _ _ hx' hy', div_eq_div_iff hn' (mul_ne_zero hx' hy')]
  constructor
  · intro h
    have h' : ((x * y : ℕ) : ℚ) = ((n * (x + y) : ℕ) : ℚ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'
  · intro h
    have h' : ((x * y : ℕ) : ℚ) = ((n * (x + y) : ℕ) : ℚ) := by rw [h]
    push_cast at h'
    linear_combination h'

/-- If d * e = n^2 and d <= n, then e >= n. -/
theorem k136404_ge {n d e : ℕ} (hn : 0 < n) (hde : d * e = n ^ 2) (hdn : d ≤ n) : n ≤ e := by
  have h1 : d * e ≤ n * e := Nat.mul_le_mul hdn (le_refl e)
  have h2 : n * n = n ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_left (by omega : n * n ≤ n * e) hn

/-- If d * e = n^2 and d >= n, then e <= n. -/
theorem k136404_le {n d e : ℕ} (hn : 0 < n) (hde : d * e = n ^ 2) (hnd : n ≤ d) : e ≤ n := by
  have h1 : n * e ≤ d * e := Nat.mul_le_mul hnd (le_refl e)
  have h2 : n * n = n ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_left (by omega : n * e ≤ n * n) hn

/-- A018892(n) is the number of divisors d <= n of n^2. -/
theorem k136404_count {n : ℕ} (hn : 0 < n) :
    OMA.S_oeis_a136404.A018892 n = ((n ^ 2).divisors.filter (fun d => d ≤ n)).card := by
  have hsq : n ^ 2 ≠ 0 := pow_ne_zero 2 hn.ne'
  have hinj : Function.Injective (fun d : ℕ => (n + d, n + n ^ 2 / d)) := by
    intro a b hab
    have h1 : n + a = n + b := congrArg Prod.fst hab
    omega
  rw [← Finset.card_image_of_injective _ hinj, ← Set.ncard_coe_finset]
  unfold OMA.S_oeis_a136404.A018892
  congr 1
  ext ⟨x, y⟩
  show (0 < x ∧ x ≤ y ∧ (1 : ℚ) / n = 1 / x + 1 / y) ↔ _
  rw [Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨hx, hxy, hq⟩
    have hy : 0 < y := by omega
    have he : x * y = n * (x + y) := (k136404_eq hn hx hy).mp hq
    have hxn : n < x := by
      by_contra hc
      have h1 : x * y ≤ n * y := Nat.mul_le_mul (by omega) (le_refl y)
      have h2 : 0 < n * x := Nat.mul_pos hn hx
      have h3 : n * (x + y) = n * x + n * y := by ring
      omega
    obtain ⟨d, rfl⟩ : ∃ d, x = n + d := ⟨x - n, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, y = n + e := ⟨y - n, by omega⟩
    have hde : d * e = n ^ 2 := by
      have h4 : (n + d) * (n + e) = n * n + n * e + d * n + d * e := by ring
      have h5 : n * (n + d + (n + e)) = n * n + n * e + d * n + n ^ 2 := by ring
      omega
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0, zero_mul] at hde
        exact absurd hde.symm hsq
      · exact h0
    have hdn : d ≤ n := by
      have h6 : d * d ≤ d * e := Nat.mul_le_mul (le_refl d) (by omega)
      have h7 : n * n = n ^ 2 := by ring
      exact Nat.mul_self_le_mul_self_iff.mp (by omega)
    refine ⟨d, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨e, hde.symm⟩, hsq⟩, hdn⟩, ?_⟩
    show (n + d, n + n ^ 2 / d) = (n + d, n + e)
    rw [← hde, Nat.mul_div_cancel_left e hd0]
  · rintro ⟨d, hd, hdeq⟩
    obtain ⟨hdv, hdn0⟩ := Finset.mem_filter.mp hd
    have hdn : d ≤ n := hdn0
    have hdvd : d ∣ n ^ 2 := (Nat.mem_divisors.mp hdv).1
    have hde : d * (n ^ 2 / d) = n ^ 2 := Nat.mul_div_cancel' hdvd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hdeq
    generalize n ^ 2 / d = e at hde ⊢
    have hen : n ≤ e := k136404_ge hn hde hdn
    refine ⟨by omega, by omega, ?_⟩
    have hp : (n + d) * (n + e) = n * (n + d + (n + e)) := by
      calc (n + d) * (n + e) = n * n + n * e + d * n + d * e := by ring
        _ = n * n + n * e + d * n + n ^ 2 := by rw [hde]
        _ = n * (n + d + (n + e)) := by ring
    exact (k136404_eq hn (by omega) (by omega)).mpr hp

/-- The divisors of n^2 that are <= n are half of them, n counted twice. -/
theorem k136404_half {n : ℕ} (hn : 0 < n) :
    2 * ((n ^ 2).divisors.filter (fun d => d ≤ n)).card = (n ^ 2).divisors.card + 1 := by
  have hsq : n ^ 2 ≠ 0 := pow_ne_zero 2 hn.ne'
  have hU : (n ^ 2).divisors.filter (fun d => d ≤ n) ∪ (n ^ 2).divisors.filter (fun d => n ≤ d) =
      (n ^ 2).divisors := by
    ext d
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      rcases le_total d n with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hI : (n ^ 2).divisors.filter (fun d => d ≤ n) ∩ (n ^ 2).divisors.filter (fun d => n ≤ d) =
      {n} := by
    ext d
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      omega
    · intro h
      rw [h]
      have hm : n ∈ (n ^ 2).divisors := Nat.mem_divisors.mpr ⟨⟨n, sq n⟩, hsq⟩
      exact ⟨⟨hm, le_refl n⟩, ⟨hm, le_refl n⟩⟩
  have hc := Finset.card_union_add_card_inter ((n ^ 2).divisors.filter (fun d => d ≤ n))
    ((n ^ 2).divisors.filter (fun d => n ≤ d))
  rw [hU, hI, Finset.card_singleton] at hc
  have hDE : ((n ^ 2).divisors.filter (fun d => d ≤ n)).card =
      ((n ^ 2).divisors.filter (fun d => n ≤ d)).card := by
    apply Finset.card_nbij' (fun d => n ^ 2 / d) (fun d => n ^ 2 / d)
    · intro d hd
      have hd' := Finset.mem_filter.mp (Finset.mem_coe.mp hd)
      have hdvd : d ∣ n ^ 2 := (Nat.mem_divisors.mp hd'.1).1
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hsq⟩, ?_⟩)
      exact k136404_ge hn (Nat.mul_div_cancel' hdvd) hd'.2
    · intro d hd
      have hd' := Finset.mem_filter.mp (Finset.mem_coe.mp hd)
      have hdvd : d ∣ n ^ 2 := (Nat.mem_divisors.mp hd'.1).1
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hsq⟩, ?_⟩)
      exact k136404_le hn (Nat.mul_div_cancel' hdvd) hd'.2
    · intro d hd
      have hd' := Finset.mem_filter.mp (Finset.mem_coe.mp hd)
      exact Nat.div_div_self (Nat.mem_divisors.mp hd'.1).1 hsq
    · intro d hd
      have hd' := Finset.mem_filter.mp (Finset.mem_coe.mp hd)
      exact Nat.div_div_self (Nat.mem_divisors.mp hd'.1).1 hsq
  omega

/-- 2 * A018892(n) = tau(n^2) + 1 for n >= 1. -/
theorem k136404_two {n : ℕ} (hn : 0 < n) :
    2 * OMA.S_oeis_a136404.A018892 n = (n ^ 2).divisors.card + 1 := by
  rw [k136404_count hn]
  exact k136404_half hn

open OMA.S_oeis_a136404 in
theorem OMA.solution : type_of% @OMA.S_oeis_a136404.main := by
  intro m
  unfold IsTermA136404 IsTermA126098
  constructor
  · rintro ⟨hpos, -, h⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      norm_num at hpos
    refine ⟨by omega, fun k hk hkm => ?_⟩
    have h1 := h (k ^ 2) (pow_pos (by omega) 2) (Nat.pow_lt_pow_left hkm two_ne_zero) ⟨k, sq k⟩
    have h2 := k136404_two (n := k) (by omega)
    have h3 := k136404_two (n := m) (by omega)
    omega
  · rintro ⟨hm, h⟩
    refine ⟨pow_pos (by omega) 2, ⟨m, sq m⟩, ?_⟩
    intro t ht htm hts
    obtain ⟨r, rfl⟩ := hts
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num at ht
    have hrm : r < m := by
      rw [sq] at htm
      exact Nat.mul_self_lt_mul_self_iff.mp htm
    have h1 := h r (by omega) hrm
    have h2 := k136404_two (n := r) (by omega)
    have h3 := k136404_two (n := m) (by omega)
    rw [← sq]
    omega
