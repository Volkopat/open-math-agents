import OMAReductions.R_erdos_634_R1_H2_R1_H2_R1_H2_R1

/-!
# Erdos 634, step erdos-634.R1.H2.R1.H2.R1.H2.R1.H1 (Lemma S: a prime at least 7 divides n)

Flattened from the Lean port of Beeson-Rosu / Bonfioli (formalizations of the triangle tiling
papers), restricted to the declarations this step uses.
-/

section
open scoped BigOperators
namespace Erdos634.LemmaS
def saw (t : ℚ) : ℚ := if Int.fract t = 0 then 0 else Int.fract t - 1 / 2
def relSpace (n : ℕ) (a : Fin 3 → ℕ) : Submodule ℚ (Fin 3 → ℚ) :=
  ⨅ (k : ℕ) (_ : k.Coprime n),
    LinearMap.ker (∑ i, saw ((k * a i : ℕ) / (n : ℚ)) •
      LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)
def trivSpace (n : ℕ) (a : Fin 3 → ℕ) : Submodule ℚ (Fin 3 → ℚ) :=
  Submodule.span ℚ ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪
                    {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})
theorem mem_relSpace {n : ℕ} {a : Fin 3 → ℕ} {e : Fin 3 → ℚ} :
    e ∈ relSpace n a ↔ ∀ k : ℕ, k.Coprime n → ∑ i, saw ((k * a i : ℕ) / (n : ℚ)) * e i = 0 := by
  simp [relSpace, Submodule.mem_iInf, LinearMap.mem_ker]
def sawZ (n m : ℕ) : ℤ := if m % n == 0 then 0 else 2 * ((m % n : ℕ) : ℤ) - n
theorem saw_eq {n : ℕ} (hn : 0 < n) (m : ℕ) :
    saw ((m : ℕ) / (n : ℚ)) = (sawZ n m : ℚ) / (2 * n) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold saw sawZ
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  by_cases h : m % n = 0
  · simp [h]
  · have h' : ((m % n : ℕ) : ℚ) / n ≠ 0 := div_ne_zero (by exact_mod_cast h) hn'
    rw [if_neg h']
    simp only [beq_iff_eq, h, if_false]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    field_simp
theorem mem_relSpace_Z {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} {e : Fin 3 → ℚ} :
    e ∈ relSpace n a ↔ ∀ k : ℕ, k.Coprime n →
      (sawZ n (k * a 0) : ℚ) * e 0 + (sawZ n (k * a 1) : ℚ) * e 1 + (sawZ n (k * a 2) : ℚ) * e 2 = 0 := by
  rw [mem_relSpace]
  have h2n : (2 * n : ℚ) ≠ 0 := by positivity
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  rw [Fin.sum_univ_three, saw_eq hn, saw_eq hn, saw_eq hn]
  constructor
  · intro h
    have := congrArg (· * (2 * n : ℚ)) h
    simp only [zero_mul] at this
    rw [← this]; field_simp
  · intro h
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      ← add_div, h, zero_div]
theorem sawZ_half {n a k : ℕ} (h : 2 * a = n) (hk : k.Coprime n) : sawZ n (k * a) = 0 := by
  have hodd : k % 2 = 1 := by
    by_contra hc
    have h2k : 2 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
    have : 2 ∣ Nat.gcd k n := Nat.dvd_gcd h2k ⟨a, h.symm⟩
    rw [hk] at this
    omega
  unfold sawZ
  by_cases ha : a = 0
  · subst ha; simp
  have hk' : k * a = (k / 2) * n + a := by
    rw [← h]
    have := Nat.div_add_mod k 2
    calc k * a = (2 * (k / 2) + k % 2) * a := by rw [this]
      _ = (k / 2) * (2 * a) + a := by rw [hodd]; ring
  have hmod : k * a % n = a := by
    rw [hk', Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  simp only [beq_iff_eq, ha, if_false]
  rw [← h]; push_cast; ring
theorem trivSpace_le (n : ℕ) (a : Fin 3 → ℕ) : trivSpace n a ≤ relSpace n a := by
  unfold trivSpace
  rw [Submodule.span_le]
  rintro v (⟨i, j, hij, haij, rfl⟩ | ⟨i, hi, rfl⟩)
  · rw [SetLike.mem_coe, mem_relSpace]
    intro k _
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp [Pi.single_apply, haij]
  · rw [SetLike.mem_coe, mem_relSpace]
    intro k hk
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [saw]
    · rw [saw_eq hn, sawZ_half hi hk]; simp
theorem two_by_two {u0 u1 v0 v1 x y : ℚ} (h1 : u0 * x + v0 * y = 0) (h2 : u1 * x + v1 * y = 0)
    (hd : u0 * v1 - u1 * v0 ≠ 0) : x = 0 ∧ y = 0 := by
  constructor
  · have : (u0 * v1 - u1 * v0) * x = 0 := by linear_combination v1 * h1 - v0 * h2
    exact (mul_eq_zero.mp this).resolve_left hd
  · have : (u0 * v1 - u1 * v0) * y = 0 := by linear_combination u0 * h2 - u1 * h1
    exact (mul_eq_zero.mp this).resolve_left hd
def det3 (p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℤ) : ℤ :=
  p0 * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)
theorem three_by_three {p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℤ} {x y z : ℚ}
    (h0 : (p0 : ℚ) * x + q0 * y + r0 * z = 0) (h1 : (p1 : ℚ) * x + q1 * y + r1 * z = 0)
    (h2 : (p2 : ℚ) * x + q2 * y + r2 * z = 0) (hd : det3 p0 q0 r0 p1 q1 r1 p2 q2 r2 ≠ 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hd' : ((det3 p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hd
  unfold det3 at hd'
  push_cast at hd'
  refine ⟨?_, ?_, ?_⟩
  · have : ((p0 : ℚ) * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)) * x
        = 0 := by
      linear_combination (↑q1 * ↑r2 - ↑r1 * ↑q2) * h0 - (↑q0 * ↑r2 - ↑r0 * ↑q2) * h1
        + (↑q0 * ↑r1 - ↑r0 * ↑q1) * h2
    exact (mul_eq_zero.mp this).resolve_left hd'
  · have : ((p0 : ℚ) * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)) * y
        = 0 := by
      linear_combination -(↑p1 * ↑r2 - ↑r1 * ↑p2) * h0 + (↑p0 * ↑r2 - ↑r0 * ↑p2) * h1
        - (↑p0 * ↑r1 - ↑r0 * ↑p1) * h2
    exact (mul_eq_zero.mp this).resolve_left hd'
  · have : ((p0 : ℚ) * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)) * z
        = 0 := by
      linear_combination (↑p1 * ↑q2 - ↑q1 * ↑p2) * h0 - (↑p0 * ↑q2 - ↑q0 * ↑p2) * h1
        + (↑p0 * ↑q1 - ↑q0 * ↑p1) * h2
    exact (mul_eq_zero.mp this).resolve_left hd'
def unitsL (n : ℕ) : List ℕ := (List.range n).filter (fun k => Nat.gcd k n == 1)
theorem coprime_of_mem_unitsL {n k : ℕ} (h : k ∈ unitsL n) : k.Coprime n := by
  unfold unitsL at h
  rw [List.mem_filter] at h
  exact beq_iff_eq.mp h.2
def minor2 (n a b : ℕ) : Bool :=
  (unitsL n).any fun k => (unitsL n).any fun k' =>
    sawZ n (k * a) * sawZ n (k' * b) - sawZ n (k' * a) * sawZ n (k * b) != 0
def minor3 (n a b c : ℕ) : Bool :=
  (unitsL n).any fun k => (unitsL n).any fun k' => (unitsL n).any fun k'' =>
    det3 (sawZ n (k * a)) (sawZ n (k * b)) (sawZ n (k * c))
      (sawZ n (k' * a)) (sawZ n (k' * b)) (sawZ n (k' * c))
      (sawZ n (k'' * a)) (sawZ n (k'' * b)) (sawZ n (k'' * c)) != 0
def cert (n a0 a1 a2 : ℕ) : Bool :=
  if a0 = a1 then minor2 n a0 a2 else if a1 = a2 then minor2 n a0 a1
  else if a0 = a2 then minor2 n a0 a1 else if 2 * a0 = n then minor2 n a1 a2
  else if 2 * a1 = n then minor2 n a0 a2 else if 2 * a2 = n then minor2 n a0 a1
  else minor3 n a0 a1 a2
def allCert (n : ℕ) : Bool :=
  (List.range n).all fun a0 => (List.range n).all fun a1 =>
    if 1 ≤ a0 ∧ 1 ≤ a1 ∧ a0 + a1 < n ∧ Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 then
      cert n a0 a1 (n - a0 - a1) else true
theorem minor2_sound {n a b : ℕ} (h : minor2 n a b = true) {x y : ℚ}
    (hrow : ∀ k : ℕ, k.Coprime n → (sawZ n (k * a) : ℚ) * x + (sawZ n (k * b) : ℚ) * y = 0) :
    x = 0 ∧ y = 0 := by
  unfold minor2 at h
  simp only [List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨k, hk, k', hk', hd⟩ := h
  refine two_by_two (hrow k (coprime_of_mem_unitsL hk)) (hrow k' (coprime_of_mem_unitsL hk')) ?_
  exact_mod_cast hd
theorem minor3_sound {n a b c : ℕ} (h : minor3 n a b c = true) {x y z : ℚ}
    (hrow : ∀ k : ℕ, k.Coprime n →
      (sawZ n (k * a) : ℚ) * x + (sawZ n (k * b) : ℚ) * y + (sawZ n (k * c) : ℚ) * z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  unfold minor3 at h
  simp only [List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨k, hk, k', hk', k'', hk'', hd⟩ := h
  exact three_by_three (hrow k (coprime_of_mem_unitsL hk)) (hrow k' (coprime_of_mem_unitsL hk'))
    (hrow k'' (coprime_of_mem_unitsL hk'')) hd
theorem pair_mem {n : ℕ} {a : Fin 3 → ℕ} {i j : Fin 3} (hij : i ≠ j) (h : a i = a j) (t : ℚ) :
    t • (Pi.single i 1 - Pi.single j 1 : Fin 3 → ℚ) ∈ trivSpace n a :=
  Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, j, hij, h, rfl⟩))
theorem half_mem {n : ℕ} {a : Fin 3 → ℕ} {i : Fin 3} (h : 2 * a i = n) (t : ℚ) :
    t • (Pi.single i 1 : Fin 3 → ℚ) ∈ trivSpace n a :=
  Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, h, rfl⟩))
theorem cert_sound {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} (hc : cert n (a 0) (a 1) (a 2) = true)
    {e : Fin 3 → ℚ} (he : e ∈ relSpace n a) : e ∈ trivSpace n a := by
  rw [mem_relSpace_Z hn] at he
  unfold cert at hc
  split_ifs at hc with h01 h12 h02 h0 h1 h2
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0 + e 1) (y := e 2) fun k hk => by
      have := he k hk; rw [← h01] at this; linear_combination this
    have : e = e 0 • (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp <;> linarith
    rw [this]; exact pair_mem (by decide) h01 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0) (y := e 1 + e 2) fun k hk => by
      have := he k hk; rw [← h12] at this; linear_combination this
    have : e = e 1 • (Pi.single 1 1 - Pi.single 2 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp <;> linarith
    rw [this]; exact pair_mem (by decide) h12 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0 + e 2) (y := e 1) fun k hk => by
      have := he k hk; rw [← h02] at this; linear_combination this
    have : e = e 0 • (Pi.single 0 1 - Pi.single 2 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp <;> linarith
    rw [this]; exact pair_mem (by decide) h02 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 1) (y := e 2) fun k hk => by
      have := he k hk; rw [sawZ_half h0 hk] at this; linear_combination this
    have : e = e 0 • (Pi.single 0 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [this]; exact half_mem h0 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0) (y := e 2) fun k hk => by
      have := he k hk; rw [sawZ_half h1 hk] at this; linear_combination this
    have : e = e 1 • (Pi.single 1 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [this]; exact half_mem h1 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0) (y := e 1) fun k hk => by
      have := he k hk; rw [sawZ_half h2 hk] at this; linear_combination this
    have : e = e 2 • (Pi.single 2 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [this]; exact half_mem h2 _
  · obtain ⟨hx, hy, hz⟩ := minor3_sound hc (x := e 0) (y := e 1) (z := e 2) fun k hk => he k hk
    have : e = 0 := by funext i; fin_cases i <;> simp [hx, hy, hz]
    rw [this]; exact Submodule.zero_mem _
theorem of_allCert {n : ℕ} (hA : allCert n = true) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace n a = trivSpace n a := by
  rw [Fin.sum_univ_three] at hsum
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  have hn : 0 < n := by omega
  have ha2 : a 2 = n - a 0 - a 1 := by omega
  unfold allCert at hA
  simp only [List.all_eq_true, List.mem_range] at hA
  have hc := hA (a 0) (by omega) (a 1) (by omega)
  rw [← ha2, if_pos ⟨h0, h1, by omega, hgcd⟩] at hc
  exact le_antisymm (fun e he => cert_sound hn hc he) (trivSpace_le n a)
def t2 (n a b : ℕ) (w : ℕ × ℕ) : Bool :=
  sawZ n (w.1 * a) * sawZ n (w.2 * b) - sawZ n (w.2 * a) * sawZ n (w.1 * b) != 0
def t3 (n a b c : ℕ) (w : ℕ × ℕ × ℕ) : Bool :=
  det3 (sawZ n (w.1 * a)) (sawZ n (w.1 * b)) (sawZ n (w.1 * c))
    (sawZ n (w.2.1 * a)) (sawZ n (w.2.1 * b)) (sawZ n (w.2.1 * c))
    (sawZ n (w.2.2 * a)) (sawZ n (w.2.2 * b)) (sawZ n (w.2.2 * c)) != 0
def isUnit (n k : ℕ) : Bool := decide (k < n) && (Nat.gcd k n == 1)
def okW (n : ℕ) (W2 : List (ℕ × ℕ)) (W3 : List (ℕ × ℕ × ℕ)) : Bool :=
  W2.all (fun w => isUnit n w.1 && isUnit n w.2) &&
    W3.all (fun w => isUnit n w.1 && (isUnit n w.2.1 && isUnit n w.2.2))
def fcert (n : ℕ) (W2 : List (ℕ × ℕ)) (W3 : List (ℕ × ℕ × ℕ)) (a0 a1 a2 : ℕ) : Bool :=
  if a0 = a1 then W2.any (t2 n a0 a2) else if a1 = a2 then W2.any (t2 n a0 a1)
  else if a0 = a2 then W2.any (t2 n a0 a1) else if 2 * a0 = n then W2.any (t2 n a1 a2)
  else if 2 * a1 = n then W2.any (t2 n a0 a2) else if 2 * a2 = n then W2.any (t2 n a0 a1)
  else W3.any (t3 n a0 a1 a2)
def fall (n : ℕ) (W2 : List (ℕ × ℕ)) (W3 : List (ℕ × ℕ × ℕ)) (lo len : ℕ) : Bool :=
  (List.range' lo len).all fun a0 => (List.range' 1 (n - 1 - a0)).all fun a1 =>
    if Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 then fcert n W2 W3 a0 a1 (n - a0 - a1) else true
theorem mem_unitsL_of {n k : ℕ} (h : isUnit n k = true) : k ∈ unitsL n := by
  unfold isUnit at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold unitsL
  rw [List.mem_filter, List.mem_range]
  exact ⟨h.1, h.2⟩
theorem minor2_of {n a b : ℕ} {W2 : List (ℕ × ℕ)} {W3 : List (ℕ × ℕ × ℕ)} (hok : okW n W2 W3 = true)
    (h : W2.any (t2 n a b) = true) : minor2 n a b = true := by
  unfold okW at hok
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hok
  rw [List.any_eq_true] at h
  obtain ⟨w, hw, ht⟩ := h
  have hu := hok.1 w hw
  rw [Bool.and_eq_true] at hu
  unfold minor2
  rw [List.any_eq_true]
  refine ⟨w.1, mem_unitsL_of hu.1, ?_⟩
  rw [List.any_eq_true]
  exact ⟨w.2, mem_unitsL_of hu.2, ht⟩
theorem minor3_of {n a b c : ℕ} {W2 : List (ℕ × ℕ)} {W3 : List (ℕ × ℕ × ℕ)} (hok : okW n W2 W3 = true)
    (h : W3.any (t3 n a b c) = true) : minor3 n a b c = true := by
  unfold okW at hok
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hok
  rw [List.any_eq_true] at h
  obtain ⟨w, hw, ht⟩ := h
  have hu := hok.2 w hw
  rw [Bool.and_eq_true, Bool.and_eq_true] at hu
  unfold minor3
  rw [List.any_eq_true]
  refine ⟨w.1, mem_unitsL_of hu.1, ?_⟩
  rw [List.any_eq_true]
  refine ⟨w.2.1, mem_unitsL_of hu.2.1, ?_⟩
  rw [List.any_eq_true]
  exact ⟨w.2.2, mem_unitsL_of hu.2.2, ht⟩
theorem fcert_sound {n : ℕ} {W2 : List (ℕ × ℕ)} {W3 : List (ℕ × ℕ × ℕ)} {a0 a1 a2 : ℕ}
    (hok : okW n W2 W3 = true) (h : fcert n W2 W3 a0 a1 a2 = true) : cert n a0 a1 a2 = true := by
  unfold fcert at h
  unfold cert
  split_ifs at h ⊢
  all_goals first | exact minor2_of hok h | exact minor3_of hok h
theorem allCert_of_fall (n len : ℕ) (W2 : List (ℕ × ℕ)) (W3 : List (ℕ × ℕ × ℕ)) (L : List ℕ)
    (hok : okW n W2 W3 = true) (hL : ∀ lo ∈ L, fall n W2 W3 lo len = true)
    (hcov : ∀ a0 < n, 1 ≤ a0 → ∃ lo ∈ L, lo ≤ a0 ∧ a0 < lo + len) : allCert n = true := by
  unfold allCert
  rw [List.all_eq_true]
  intro a0 ha0
  rw [List.mem_range] at ha0
  rw [List.all_eq_true]
  intro a1 ha1
  rw [List.mem_range] at ha1
  split_ifs with hc
  · obtain ⟨lo, hlo, h1, h2⟩ := hcov a0 ha0 hc.1
    have h3 := hL lo hlo
    unfold fall at h3
    rw [List.all_eq_true] at h3
    have h4 := h3 a0 (by rw [List.mem_range']; exact ⟨a0 - lo, by omega, by omega⟩)
    rw [List.all_eq_true] at h4
    have h5 := h4 a1 (by rw [List.mem_range']; exact ⟨a1 - 1, by omega, by omega⟩)
    rw [if_pos hc.2.2.2] at h5
    exact fcert_sound hok h5
  · rfl
def W2_21 : List (ℕ × ℕ) := [(1, 2)]
def W3_21 : List (ℕ × ℕ × ℕ) := [(1, 2, 5), (1, 2, 10)]
theorem allCert_21 : allCert 21 = true := by
  refine allCert_of_fall 21 21 W2_21 W3_21 [1] (by decide +kernel) ?_ (by decide +kernel)
  intro lo hlo
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
  subst hlo
  decide +kernel
def W2_28 : List (ℕ × ℕ) := [(1, 3)]
def W3_28 : List (ℕ × ℕ × ℕ) := [(1, 3, 11), (1, 5, 9), (1, 3, 13)]
theorem allCert_28 : allCert 28 = true := by
  refine allCert_of_fall 28 28 W2_28 W3_28 [1] (by decide +kernel) ?_ (by decide +kernel)
  intro lo hlo
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
  subst hlo
  decide +kernel
def W2_42 : List (ℕ × ℕ) := [(1, 5)]
def W3_42 : List (ℕ × ℕ × ℕ) := [(1, 5, 13), (1, 11, 17), (1, 5, 19)]
theorem allCert_42 : allCert 42 = true := by
  refine allCert_of_fall 42 23 W2_42 W3_42 [1, 24] (by decide +kernel) ?_ (by decide +kernel)
  intro lo hlo
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
  rcases hlo with rfl | rfl
  · decide +kernel
  · decide +kernel
def W2_66 : List (ℕ × ℕ) := [(1, 5)]
def W3_66 : List (ℕ × ℕ × ℕ) := [(1, 5, 23), (1, 13, 17), (1, 7, 19), (1, 25, 29), (1, 5, 31)]
theorem allCert_66 : allCert 66 = true := by
  refine allCert_of_fall 66 15 W2_66 W3_66 [1, 16, 31, 46, 61] (by decide +kernel) ?_ (by decide +kernel)
  intro lo hlo
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
  rcases hlo with rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem lemmaS_finite {n : ℕ} (hn : n = 21 ∨ n = 28 ∨ n = 42 ∨ n = 66) (a : Fin 3 → ℕ)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace n a = trivSpace n a := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact of_allCert allCert_21 a hpos hsum hgcd
  · exact of_allCert allCert_28 a hpos hsum hgcd
  · exact of_allCert allCert_42 a hpos hsum hgcd
  · exact of_allCert allCert_66 a hpos hsum hgcd
end Erdos634.LemmaS
end

section
open scoped BigOperators
namespace Erdos634.CaseA.R0c
open Erdos634.LemmaS
variable {N : ℕ}
def LemmaSStatement : Prop :=
  ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 →
    ∀ p : ℕ, p.Prime → 7 ≤ p → p ∣ n → relSpace n a = trivSpace n a
end Erdos634.CaseA.R0c
end

section
open scoped BigOperators
open Complex DirichletCharacter HurwitzZeta
namespace Erdos634.LemmaSB1
variable {N : ℕ} [NeZero N]
theorem gaussSum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro h
  have h0 : ZMod.dft (χ : ZMod N → ℂ) = 0 := funext fun k => by
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, h, mul_zero]; rfl
  have := congr_fun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [h0, map_zero, neg_neg, MulChar.map_one] at this
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [Pi.zero_apply, smul_eq_mul, mul_one] at this
  exact hN this.symm
theorem level_ne_one_of_odd {χ : DirichletCharacter ℂ N} (ho : χ.Odd) : N ≠ 1 := by
  rintro rfl
  have h1 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
  have : χ (-1) = -1 := ho
  rw [h1, MulChar.map_one] at this
  norm_num at this
theorem ne_one_of_odd {χ : DirichletCharacter ℂ N} (ho : χ.Odd) : χ ≠ 1 := by
  rintro rfl
  have : (1 : DirichletCharacter ℂ N) (-1) = -1 := ho
  rw [MulChar.one_apply (isUnit_one.neg)] at this
  norm_num at this
theorem inv_odd {χ : DirichletCharacter ℂ N} (ho : χ.Odd) : χ⁻¹.Odd := by
  show χ⁻¹ (-1) = -1
  rw [MulChar.inv_apply_eq_inv', ho]; norm_num
theorem LFunction_zero_ne_zero {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (ho : χ.Odd) :
    LFunction χ 0 ≠ 0 := by
  have hN := level_ne_one_of_odd ho
  rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hN), ho.gammaFactor_def, zero_add,
    Gammaℝ_one, div_one]
  have hfe := hp.completedLFunction_one_sub 1
  rw [sub_self] at hfe
  rw [hfe]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcp : ∀ w : ℂ, (N : ℂ) ^ w ≠ 0 := fun w => by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  refine mul_ne_zero (mul_ne_zero (hcp _) ?_) ?_
  · unfold rootNumber
    exact div_ne_zero (div_ne_zero (gaussSum_ne_zero hp) (pow_ne_zero _ I_ne_zero)) (hcp _)
  · intro h0
    have hL := LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inl one_ne_zero)
    rw [(inv_odd ho).gammaFactor_def, h0, zero_div] at hL
    exact LFunction_apply_one_ne_zero (inv_ne_one.mpr (ne_one_of_odd ho)) hL
theorem LFunction_zero_eq {χ : DirichletCharacter ℂ N} (ho : χ.Odd) :
    LFunction χ 0 = ∑ j : ZMod N, χ j * hurwitzZetaOdd (ZMod.toAddCircle j) 0 := by
  have := ZMod.LFunction_def_odd ho.to_fun 0
  rw [neg_zero, cpow_zero, one_mul] at this
  exact this
def HurwitzOddZero : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → hurwitzZetaOdd (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ)
theorem saw_val {j : ZMod N} (hj : j ≠ 0) :
    ((Erdos634.LemmaS.saw ((j.val : ℚ) / N) : ℚ) : ℂ) = (j.val : ℂ) / N - 1 / 2 := by
  have hv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj
  have hlt : j.val < N := ZMod.val_lt j
  have hNq : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hf : Int.fract ((j.val : ℚ) / N) = (j.val : ℚ) / N := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, (div_lt_one hNq).mpr (by exact_mod_cast hlt)⟩
  have hne : (j.val : ℚ) / N ≠ 0 := div_ne_zero (by exact_mod_cast hv) hNq.ne'
  unfold Erdos634.LemmaS.saw
  rw [hf, if_neg hne]
  push_cast; ring
theorem B1_of_hurwitzOddZero (H : HurwitzOddZero) {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (ho : χ.Odd) :
    ∑ j : ZMod N, χ j * ((Erdos634.LemmaS.saw ((j.val : ℚ) / N) : ℚ) : ℂ) ≠ 0 := by
  have hN := level_ne_one_of_odd ho
  have key : ∀ j : ZMod N, χ j * hurwitzZetaOdd (ZMod.toAddCircle j) 0 =
      -(χ j * ((Erdos634.LemmaS.saw ((j.val : ℚ) / N) : ℚ) : ℂ)) := by
    intro j
    by_cases hj : j = 0
    · subst hj; rw [χ.map_zero' hN]; simp
    · have hv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj
      have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      rw [ZMod.toAddCircle_apply, H _ (by positivity)
        ((div_lt_one hNr).mpr (by exact_mod_cast ZMod.val_lt j)), saw_val hj]
      push_cast; ring
  intro hsum
  apply LFunction_zero_ne_zero hp ho
  rw [LFunction_zero_eq ho, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_neg_distrib, hsum,
    neg_zero]
end Erdos634.LemmaSB1
end

section
namespace Erdos634.DirichletCRT
open DirichletCharacter
variable {R : Type*} [CommMonoidWithZero R] {m₁ m₂ : ℕ}
noncomputable def unitsCRT (h : m₁.Coprime m₂) : (ZMod (m₁ * m₂))ˣ ≃* (ZMod m₁)ˣ × (ZMod m₂)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
theorem unitsCRT_fst (h : m₁.Coprime m₂) (x : (ZMod (m₁ * m₂))ˣ) :
    (unitsCRT h x).1 = ZMod.unitsMap (Nat.dvd_mul_right m₁ m₂) x := by
  have key : (RingHom.fst (ZMod m₁) (ZMod m₂)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (Nat.dvd_mul_right m₁ m₂) (ZMod m₁) := RingHom.ext_zmod _ _
  ext
  have := congrArg (fun f => f (x : ZMod (m₁ * m₂))) key
  simp only [RingHom.comp_apply, RingHom.coe_fst, ZMod.castHom_apply] at this
  simp [unitsCRT, MulEquiv.prodUnits, ZMod.unitsMap_val, ← this]
theorem unitsCRT_snd (h : m₁.Coprime m₂) (x : (ZMod (m₁ * m₂))ˣ) :
    (unitsCRT h x).2 = ZMod.unitsMap (Nat.dvd_mul_left m₂ m₁) x := by
  have key : (RingHom.snd (ZMod m₁) (ZMod m₂)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (Nat.dvd_mul_left m₂ m₁) (ZMod m₂) := RingHom.ext_zmod _ _
  ext
  have := congrArg (fun f => f (x : ZMod (m₁ * m₂))) key
  simp only [RingHom.comp_apply, RingHom.coe_snd, ZMod.castHom_apply] at this
  simp [unitsCRT, MulEquiv.prodUnits, ZMod.unitsMap_val, ← this]
theorem changeLevel_unit {n m : ℕ} (hm : n ∣ m) (ψ : DirichletCharacter R n) (x : (ZMod m)ˣ) :
    changeLevel hm ψ (x : ZMod m) = ψ (ZMod.unitsMap hm x : ZMod n) := by
  rw [changeLevel_def, MulChar.ofUnitHom_coe]
  simp
noncomputable def comp₁ (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) :
    DirichletCharacter R m₁ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp ((unitsCRT h).symm.toMonoidHom.comp (MonoidHom.inl _ _)))
noncomputable def comp₂ (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) :
    DirichletCharacter R m₂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp ((unitsCRT h).symm.toMonoidHom.comp (MonoidHom.inr _ _)))
theorem comp₁_unit (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) (a : (ZMod m₁)ˣ) :
    comp₁ h χ (a : ZMod m₁) = χ (((unitsCRT h).symm (a, 1) : (ZMod (m₁ * m₂))ˣ) : ZMod (m₁ * m₂)) := by
  rw [comp₁, MulChar.ofUnitHom_coe]; simp
theorem comp₂_unit (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) (b : (ZMod m₂)ˣ) :
    comp₂ h χ (b : ZMod m₂) = χ (((unitsCRT h).symm (1, b) : (ZMod (m₁ * m₂))ˣ) : ZMod (m₁ * m₂)) := by
  rw [comp₂, MulChar.ofUnitHom_coe]; simp
theorem decomp (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) :
    χ = changeLevel (Nat.dvd_mul_right m₁ m₂) (comp₁ h χ) *
      changeLevel (Nat.dvd_mul_left m₂ m₁) (comp₂ h χ) := by
  ext x
  rw [MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_unit, changeLevel_unit, comp₁_unit,
    comp₂_unit, ← unitsCRT_fst h, ← unitsCRT_snd h, ← map_mul, ← Units.val_mul, ← map_mul]
  simp
theorem prod_unit (h : m₁.Coprime m₂) (ψ : DirichletCharacter R m₁) (η : DirichletCharacter R m₂)
    (x : (ZMod (m₁ * m₂))ˣ) :
    (changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η)
      (x : ZMod (m₁ * m₂)) = ψ ((unitsCRT h x).1 : ZMod m₁) * η ((unitsCRT h x).2 : ZMod m₂) := by
  rw [MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_unit, changeLevel_unit, unitsCRT_fst,
    unitsCRT_snd]
theorem decomp_unique (h : m₁.Coprime m₂) {ψ ψ' : DirichletCharacter R m₁}
    {η η' : DirichletCharacter R m₂}
    (he : changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η =
      changeLevel (Nat.dvd_mul_right m₁ m₂) ψ' * changeLevel (Nat.dvd_mul_left m₂ m₁) η') :
    ψ = ψ' ∧ η = η' := by
  constructor
  · ext a
    have := congrArg (fun χ : DirichletCharacter R (m₁ * m₂) =>
      χ (((unitsCRT h).symm (a, 1) : (ZMod (m₁ * m₂))ˣ) : ZMod (m₁ * m₂))) he
    simpa [prod_unit h] using this
  · ext b
    have := congrArg (fun χ : DirichletCharacter R (m₁ * m₂) =>
      χ (((unitsCRT h).symm (1, b) : (ZMod (m₁ * m₂))ˣ) : ZMod (m₁ * m₂))) he
    simpa [prod_unit h] using this
section FT
variable (h : m₁.Coprime m₂) {χ : DirichletCharacter R (m₁ * m₂)}
  {ψ : DirichletCharacter R m₁} {η : DirichletCharacter R m₂}
  (hχ : χ = changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η)
include h hχ
theorem factorsThrough_mul_of {d₁ d₂ : ℕ} (h₁ : ψ.FactorsThrough d₁) (h₂ : η.FactorsThrough d₂) :
    χ.FactorsThrough (d₁ * d₂) := by
  obtain ⟨hd₁, ψ₀, rfl⟩ := h₁
  obtain ⟨hd₂, η₀, rfl⟩ := h₂
  refine ⟨Nat.mul_dvd_mul hd₁ hd₂, changeLevel (Nat.dvd_mul_right d₁ d₂) ψ₀ *
    changeLevel (Nat.dvd_mul_left d₂ d₁) η₀, ?_⟩
  rw [hχ, map_mul, ← changeLevel_trans, ← changeLevel_trans, ← changeLevel_trans,
    ← changeLevel_trans]
theorem factorsThrough_of_mul {d₁ d₂ : ℕ} (hd₁ : d₁ ∣ m₁) (hd₂ : d₂ ∣ m₂)
    (hf : χ.FactorsThrough (d₁ * d₂)) : ψ.FactorsThrough d₁ ∧ η.FactorsThrough d₂ := by
  have hd : d₁.Coprime d₂ := (h.coprime_dvd_left hd₁).coprime_dvd_right hd₂
  obtain ⟨hdd, χ₀, hχ₀⟩ := hf
  have e := decomp hd χ₀
  have key : χ = changeLevel (Nat.dvd_mul_right m₁ m₂) (changeLevel hd₁ (comp₁ hd χ₀)) *
      changeLevel (Nat.dvd_mul_left m₂ m₁) (changeLevel hd₂ (comp₂ hd χ₀)) := by
    rw [hχ₀]
    conv_lhs => rw [e]
    rw [map_mul, ← changeLevel_trans, ← changeLevel_trans, ← changeLevel_trans,
      ← changeLevel_trans]
  obtain ⟨e1, e2⟩ := decomp_unique h (hχ.symm.trans key)
  exact ⟨⟨hd₁, _, e1⟩, ⟨hd₂, _, e2⟩⟩
theorem conductor_eq [NeZero m₁] [NeZero m₂] :
    χ.conductor = ψ.conductor * η.conductor := by
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  apply Nat.dvd_antisymm
  · exact conductor_dvd_of_mem_conductorSet _
      (factorsThrough_mul_of h hχ (factorsThrough_conductor ψ) (factorsThrough_conductor η))
  · set c := χ.conductor
    have hc : c = c.gcd m₁ * c.gcd m₂ := by
      rw [← Nat.Coprime.gcd_mul c h, Nat.gcd_eq_left (conductor_dvd_level χ)]
    have hf : χ.FactorsThrough (c.gcd m₁ * c.gcd m₂) := hc ▸ factorsThrough_conductor χ
    obtain ⟨f1, f2⟩ := factorsThrough_of_mul h hχ (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _) hf
    rw [hc]
    exact Nat.mul_dvd_mul (conductor_dvd_of_mem_conductorSet ψ f1)
      (conductor_dvd_of_mem_conductorSet η f2)
theorem primitiveCharacter_eq [NeZero m₁] [NeZero m₂] :
    χ.primitiveCharacter =
      changeLevel (show ψ.conductor ∣ χ.conductor by
          rw [conductor_eq h hχ]; exact Nat.dvd_mul_right _ _) ψ.primitiveCharacter *
      changeLevel (show η.conductor ∣ χ.conductor by
          rw [conductor_eq h hχ]; exact Nat.dvd_mul_left _ _) η.primitiveCharacter := by
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  apply changeLevel_injective (conductor_dvd_level χ)
  rw [changeLevel_primitiveCharacter, map_mul, ← changeLevel_trans, ← changeLevel_trans]
  conv_lhs => rw [hχ]
  congr 1
  · conv_lhs => rw [← changeLevel_primitiveCharacter ψ]
    rw [← changeLevel_trans]
  · conv_lhs => rw [← changeLevel_primitiveCharacter η]
    rw [← changeLevel_trans]
theorem isPrimitive_iff [NeZero m₁] [NeZero m₂] :
    χ.IsPrimitive ↔ ψ.IsPrimitive ∧ η.IsPrimitive := by
  simp only [isPrimitive_def, conductor_eq h hχ]
  have a1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m₁)) (conductor_dvd_level ψ)
  have a2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m₂)) (conductor_dvd_level η)
  have p1 : 0 < ψ.conductor := Nat.pos_of_ne_zero (conductor_ne_zero ψ)
  have p2 : 0 < η.conductor := Nat.pos_of_ne_zero (conductor_ne_zero η)
  constructor
  · intro e
    constructor
    · by_contra hne
      have : ψ.conductor < m₁ := lt_of_le_of_ne a1 hne
      have := Nat.mul_lt_mul_of_lt_of_le this a2 (Nat.pos_of_ne_zero (NeZero.ne m₂))
      omega
    · by_contra hne
      have : η.conductor < m₂ := lt_of_le_of_ne a2 hne
      have := Nat.mul_lt_mul_of_le_of_lt a1 this (Nat.pos_of_ne_zero (NeZero.ne m₁))
      omega
  · rintro ⟨e1, e2⟩; rw [e1, e2]
end FT
theorem unit_val_ne_zero {n : ℕ} (ψ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ψ (a : ZMod n) ≠ 0 := by
  rw [← MulChar.coe_toUnitHom]; exact Units.ne_zero _
theorem const_iff (h : m₁.Coprime m₂) [NeZero m₁] [NeZero m₂] (g : (ZMod (m₁ * m₂))ˣ)
    (hne₁ : ∃ ψ : DirichletCharacter ℂ m₁, ψ.IsPrimitive)
    (hne₂ : ∃ η : DirichletCharacter ℂ m₂, η.IsPrimitive) :
    (∃ c : ℂ, ∀ χ : DirichletCharacter ℂ (m₁ * m₂), χ.IsPrimitive → χ (g : ZMod (m₁ * m₂)) = c) ↔
    (∃ c₁ : ℂ, ∀ ψ : DirichletCharacter ℂ m₁, ψ.IsPrimitive → ψ ((unitsCRT h g).1 : ZMod m₁) = c₁) ∧
    (∃ c₂ : ℂ, ∀ η : DirichletCharacter ℂ m₂, η.IsPrimitive → η ((unitsCRT h g).2 : ZMod m₂) = c₂) := by
  obtain ⟨ψ₀, hψ₀⟩ := hne₁
  obtain ⟨η₀, hη₀⟩ := hne₂
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c / η₀ ((unitsCRT h g).2 : ZMod m₂), fun ψ hψ => ?_⟩,
      ⟨c / ψ₀ ((unitsCRT h g).1 : ZMod m₁), fun η hη => ?_⟩⟩
    · have := hc _ ((isPrimitive_iff h (ψ := ψ) (η := η₀) rfl).2 ⟨hψ, hη₀⟩)
      rw [prod_unit h] at this
      rw [← this, mul_div_cancel_right₀ _ (unit_val_ne_zero _ _)]
    · have := hc _ ((isPrimitive_iff h (ψ := ψ₀) (η := η) rfl).2 ⟨hψ₀, hη⟩)
      rw [prod_unit h] at this
      rw [← this, mul_div_cancel_left₀ _ (unit_val_ne_zero _ _)]
  · rintro ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩
    refine ⟨c₁ * c₂, fun χ hχ => ?_⟩
    have e := decomp h χ
    obtain ⟨p1, p2⟩ := (isPrimitive_iff h e).1 hχ
    rw [e, prod_unit h, h₁ _ p1, h₂ _ p2]
end Erdos634.DirichletCRT
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSC
open Erdos634.LemmaS (saw)
noncomputable def sN (M x : ℕ) : ℂ := ((saw ((x : ℚ) / M) : ℚ) : ℂ)
theorem saw_add_nat (t : ℚ) (m : ℕ) : saw (t + m) = saw t := by
  unfold saw; rw [Int.fract_add_natCast]
theorem sN_mod (M x : ℕ) : sN M x = sN M (x % M) := by
  unfold sN
  congr 1
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  · have hM : (M : ℚ) ≠ 0 := by exact_mod_cast h.ne'
    have hq : (x : ℚ) = ((x % M : ℕ) : ℚ) + (M : ℚ) * ((x / M : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mod_add_div x M).symm
    rw [hq, add_div, mul_div_cancel_left₀ _ hM, saw_add_nat]
theorem sN_mul {d : ℕ} (hd : 0 < d) (M y : ℕ) : sN (d * M) (d * y) = sN M y := by
  unfold sN
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  rw [mul_div_mul_left _ _ hd']
theorem sN_lt {M x : ℕ} (hx : x < M) :
    sN M x = if x = 0 then 0 else (x : ℂ) / M - 1 / 2 := by
  unfold sN saw
  have hM : (0 : ℚ) < M := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le x) hx)
  have hf : Int.fract ((x : ℚ) / M) = (x : ℚ) / M := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, (div_lt_one hM).mpr (by exact_mod_cast hx)⟩
  rw [hf]
  by_cases h0 : x = 0
  · subst h0; simp
  · have hne : (x : ℚ) / M ≠ 0 := div_ne_zero (by exact_mod_cast h0) hM.ne'
    rw [if_neg hne, if_neg h0]
    push_cast; ring
theorem sum_range_mul_block (G : ℕ → ℂ) (f k : ℕ) :
    ∑ x ∈ range (f * k), G x = ∑ t ∈ range k, ∑ y ∈ range f, G (f * t + y) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
theorem sum_range_cast_mul_two (m : ℕ) : (∑ t ∈ range m, (t : ℂ)) * 2 = m * ((m : ℂ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring
theorem dist {f k y : ℕ} (hk : 0 < k) (hy : y < f) :
    ∑ t ∈ range k, sN (f * k) (f * t + y) = sN f y := by
  have hf : 0 < f := lt_of_le_of_lt (Nat.zero_le y) hy
  have hlt : ∀ t ∈ range k, f * t + y < f * k := by
    intro t ht
    have := mem_range.1 ht
    calc f * t + y < f * t + f := by omega
      _ = f * (t + 1) := by ring
      _ ≤ f * k := Nat.mul_le_mul_left f this
  have hfC : (f : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hS := sum_range_cast_mul_two k
  by_cases hy0 : y = 0
  · subst hy0
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [sum_range_succ']
    have hterm : ∀ t ∈ range k', sN (f * (k' + 1)) (f * (t + 1) + 0)
        = (t : ℂ) * (1 / ((k' : ℂ) + 1)) + (1 / ((k' : ℂ) + 1) - 1 / 2) := by
      intro t ht
      rw [sN_lt (hlt (t + 1) (by simp at ht ⊢; omega)), if_neg (by positivity)]
      have hk1 : (k' : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k')
      push_cast; field_simp; ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← sum_mul, sum_const, card_range, nsmul_eq_mul,
      show f * 0 + 0 = 0 by simp, sN_lt (show 0 < f * (k' + 1) by positivity), if_pos rfl,
      sN_lt hy, if_pos rfl, add_zero]
    have hS' := sum_range_cast_mul_two k'
    have hk1 : (k' : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k')
    have : (∑ t ∈ range k', (t : ℂ)) = k' * ((k' : ℂ) - 1) / 2 := by
      rw [eq_div_iff (two_ne_zero)]; exact hS'
    rw [this]; field_simp; ring
  · have hterm : ∀ t ∈ range k, sN (f * k) (f * t + y)
        = (t : ℂ) * (1 / k) + ((y : ℂ) / (f * k) - 1 / 2) := by
      intro t ht
      rw [sN_lt (hlt t ht), if_neg (by omega)]
      push_cast; field_simp; ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← sum_mul, sum_const, card_range, nsmul_eq_mul,
      sN_lt hy, if_neg hy0]
    have : (∑ t ∈ range k, (t : ℂ)) = k * ((k : ℂ) - 1) / 2 := by
      rw [eq_div_iff (two_ne_zero)]; exact hS
    rw [this]; field_simp; ring
noncomputable def B {f : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) : ℂ :=
  ∑ y : ZMod f, ω y * ((saw ((y.val : ℚ) / f) : ℚ) : ℂ)
theorem sum_zmod_eq_range {f : ℕ} [NeZero f] (G : ZMod f → ℂ) :
    ∑ y : ZMod f, G y = ∑ i ∈ range f, G (i : ZMod f) := by
  refine Finset.sum_nbij' (fun y => y.val) (fun i => (i : ZMod f)) ?_ ?_ ?_ ?_ ?_
  · intro y _; simp [ZMod.val_lt]
  · intro i _; simp
  · intro y _; simp
  · intro i hi; simp [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 hi)]
  · intro y _; simp
theorem B_eq_range {f : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) :
    B ω = ∑ i ∈ range f, ω (i : ZMod f) * sN f i := by
  unfold B
  rw [sum_zmod_eq_range]
  refine sum_congr rfl (fun i hi => ?_)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 hi)]
  rfl
noncomputable def A {f : ℕ} (ω : DirichletCharacter ℂ f) (M : ℕ) : ℂ :=
  ∑ x ∈ range M, ω (x : ZMod f) * sN M x
theorem A_eq {f k : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) (hk : 0 < k) :
    A ω (f * k) = B ω := by
  unfold A
  rw [sum_range_mul_block, sum_comm, B_eq_range]
  refine sum_congr rfl (fun y hy => ?_)
  have hω : ∀ t, ω (((f * t + y : ℕ)) : ZMod f) = ω (y : ZMod f) := by
    intro t; push_cast; rw [ZMod.natCast_self, zero_mul, zero_add]
  simp_rw [hω, ← mul_sum]
  rw [dist hk (mem_range.1 hy)]
theorem prod_one_sub (P : Finset ℕ) (c : ℕ → ℂ) :
    ∏ ℓ ∈ P, (1 - c ℓ) = ∑ D ∈ P.powerset, (-1 : ℂ) ^ D.card * ∏ ℓ ∈ D, c ℓ := by
  have h := Finset.prod_add (fun ℓ => -c ℓ) (fun _ => (1 : ℂ)) P
  simp only [prod_const_one, mul_one] at h
  rw [show ∏ ℓ ∈ P, (1 - c ℓ) = ∏ ℓ ∈ P, (-c ℓ + 1) from prod_congr rfl (fun _ _ => by ring), h]
  refine sum_congr rfl (fun D _ => ?_)
  rw [show ∏ ℓ ∈ D, -c ℓ = ∏ ℓ ∈ D, ((-1) * c ℓ) from prod_congr rfl (fun _ _ => by ring),
    prod_mul_distrib, prod_const]
theorem prod_ind {D : Finset ℕ} (hD : ∀ ℓ ∈ D, ℓ.Prime) (x : ℕ) :
    ∏ ℓ ∈ D, (if ℓ ∣ x then (1 : ℂ) else 0) = if (∏ ℓ ∈ D, ℓ) ∣ x then 1 else 0 := by
  by_cases h : ∀ ℓ ∈ D, ℓ ∣ x
  · rw [prod_eq_one (fun ℓ hℓ => if_pos (h ℓ hℓ)), if_pos]
    exact Finset.prod_primes_dvd x (fun ℓ hℓ => (hD ℓ hℓ).prime) h
  · push Not at h
    obtain ⟨ℓ, hℓ, hn⟩ := h
    rw [prod_eq_zero hℓ (if_neg hn), if_neg]
    exact fun hd => hn (dvd_trans (dvd_prod_of_mem _ hℓ) hd)
theorem inner {f d M : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) (hd : 0 < d) (hdM : d ∣ M)
    (hcop : d.Coprime f) (hfM : f ∣ M) (hM : 0 < M) :
    ∑ x ∈ range M, (if d ∣ x then (1 : ℂ) else 0) * ω (x : ZMod f) * sN M x
      = ω (d : ZMod f) * B ω := by
  obtain ⟨M', rfl⟩ := hdM
  have hfM' : f ∣ M' := hcop.symm.dvd_of_dvd_mul_left hfM
  obtain ⟨k, rfl⟩ := hfM'
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hM
    · exact h
  rw [sum_range_mul_block]
  have hin : ∀ t ∈ range (f * k), ∑ r ∈ range d,
      (if d ∣ d * t + r then (1 : ℂ) else 0) * ω ((d * t + r : ℕ) : ZMod f) * sN (d * (f * k)) (d * t + r)
      = ω (d : ZMod f) * (ω (t : ZMod f) * sN (f * k) t) := by
    intro t _
    rw [Finset.sum_eq_single 0]
    · rw [add_zero, if_pos (dvd_mul_right d t), one_mul, sN_mul hd]
      push_cast; rw [map_mul]; ring
    · intro r hr hr0
      rw [if_neg, zero_mul, zero_mul]
      intro hdv
      have : d ∣ r := (Nat.dvd_add_right (dvd_mul_right d t)).mp hdv
      exact hr0 (Nat.eq_zero_of_dvd_of_lt this (mem_range.1 hr))
    · intro h; exact absurd (mem_range.2 hd) h
  rw [sum_congr rfl hin, ← mul_sum]
  change ω (d : ZMod f) * A ω (f * k) = _
  rw [A_eq ω hk]
def eulerPrimes (M f : ℕ) : Finset ℕ := M.primeFactors.filter (fun ℓ => ¬ ℓ ∣ f)
theorem T_eq {f M : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) (hfM : f ∣ M) (hM : 0 < M) :
    ∑ x ∈ range M, (if x.Coprime M then ω (x : ZMod f) else 0) * sN M x
      = B ω * ∏ ℓ ∈ eulerPrimes M f, (1 - ω (ℓ : ZMod f)) := by
  set P := eulerPrimes M f with hP
  have hPmem : ∀ ℓ ∈ P, ℓ.Prime ∧ ℓ ∣ M ∧ ¬ ℓ ∣ f := by
    intro ℓ hℓ
    obtain ⟨h1, h2⟩ := mem_filter.1 hℓ
    exact ⟨Nat.prime_of_mem_primeFactors h1, Nat.dvd_of_mem_primeFactors h1, h2⟩
  have key : ∀ x, (if x.Coprime M then ω (x : ZMod f) else 0)
      = (∏ ℓ ∈ P, (1 - if ℓ ∣ x then (1 : ℂ) else 0)) * ω (x : ZMod f) := by
    intro x
    by_cases hc : x.Coprime M
    · rw [if_pos hc, prod_eq_one, one_mul]
      intro ℓ hℓ
      obtain ⟨hp, hℓM, _⟩ := hPmem ℓ hℓ
      rw [if_neg, sub_zero]
      intro hdx
      have := Nat.dvd_gcd hdx hℓM
      rw [Nat.Coprime.gcd_eq_one hc] at this
      exact hp.not_dvd_one this
    · rw [if_neg hc]
      have hg : Nat.gcd x M ≠ 1 := hc
      have hp := Nat.minFac_prime hg
      have hℓx : (Nat.gcd x M).minFac ∣ x := dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left x M)
      have hℓM : (Nat.gcd x M).minFac ∣ M := dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right x M)
      by_cases hℓf : (Nat.gcd x M).minFac ∣ f
      · rw [MulChar.map_nonunit ω, mul_zero]
        rw [ZMod.isUnit_iff_coprime]
        intro hcop
        have := Nat.dvd_gcd hℓx hℓf
        rw [Nat.Coprime.gcd_eq_one hcop] at this
        exact hp.not_dvd_one this
      · rw [prod_eq_zero (i := (Nat.gcd x M).minFac), zero_mul]
        · exact mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hℓM, hM.ne'⟩, hℓf⟩
        · rw [if_pos hℓx, sub_self]
  have hDprops : ∀ D ∈ P.powerset, 0 < ∏ ℓ ∈ D, ℓ ∧ (∏ ℓ ∈ D, ℓ) ∣ M ∧ (∏ ℓ ∈ D, ℓ).Coprime f
      ∧ ∀ ℓ ∈ D, ℓ.Prime := by
    intro D hD
    have hsub := mem_powerset.1 hD
    have hpr : ∀ ℓ ∈ D, ℓ.Prime := fun ℓ hℓ => (hPmem ℓ (hsub hℓ)).1
    refine ⟨prod_pos (fun ℓ hℓ => (hpr ℓ hℓ).pos), ?_, ?_, hpr⟩
    · exact Finset.prod_primes_dvd M (fun ℓ hℓ => (hpr ℓ hℓ).prime)
        (fun ℓ hℓ => (hPmem ℓ (hsub hℓ)).2.1)
    · exact Nat.Coprime.prod_left (fun ℓ hℓ =>
        (Nat.Prime.coprime_iff_not_dvd (hpr ℓ hℓ)).2 (hPmem ℓ (hsub hℓ)).2.2)
  calc ∑ x ∈ range M, (if x.Coprime M then ω (x : ZMod f) else 0) * sN M x
      = ∑ x ∈ range M, ∑ D ∈ P.powerset, (-1 : ℂ) ^ D.card *
          ((if (∏ ℓ ∈ D, ℓ) ∣ x then (1 : ℂ) else 0) * ω (x : ZMod f) * sN M x) := by
        refine sum_congr rfl (fun x _ => ?_)
        rw [key, prod_one_sub, sum_mul, sum_mul]
        refine sum_congr rfl (fun D hD => ?_)
        rw [prod_ind (hDprops D hD).2.2.2]
        ring
    _ = ∑ D ∈ P.powerset, (-1 : ℂ) ^ D.card * ∑ x ∈ range M,
          (if (∏ ℓ ∈ D, ℓ) ∣ x then (1 : ℂ) else 0) * ω (x : ZMod f) * sN M x := by
        rw [sum_comm]
        refine sum_congr rfl (fun D _ => ?_)
        rw [mul_sum]
    _ = ∑ D ∈ P.powerset, (-1 : ℂ) ^ D.card * (ω ((∏ ℓ ∈ D, ℓ : ℕ) : ZMod f) * B ω) := by
        refine sum_congr rfl (fun D hD => ?_)
        obtain ⟨h1, h2, h3, _⟩ := hDprops D hD
        rw [inner ω h1 h2 h3 hfM hM]
    _ = B ω * ∏ ℓ ∈ P, (1 - ω (ℓ : ZMod f)) := by
        rw [prod_one_sub, mul_sum]
        refine sum_congr rfl (fun D _ => ?_)
        rw [Nat.cast_prod, map_prod]
        ring
theorem sum_units_eq_sum {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (F : ZMod M → ℂ) :
    ∑ u : (ZMod M)ˣ, χ u * F u = ∑ x : ZMod M, χ x * F x := by
  symm
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.map ⟨(Units.val : (ZMod M)ˣ → ZMod M), Units.val_injective⟩))]
  · rw [Finset.sum_map]; rfl
  · intro x _ hx
    have : ¬ IsUnit x := by
      rintro ⟨u, rfl⟩
      exact hx (by simp)
    rw [MulChar.map_nonunit χ this, zero_mul]
theorem sum_units_changeLevel {f M : ℕ} [NeZero f] [NeZero M] (ω : DirichletCharacter ℂ f)
    (hfM : f ∣ M) :
    ∑ u : (ZMod M)ˣ, DirichletCharacter.changeLevel hfM ω (u : ZMod M) * sN M (u : ZMod M).val
      = B ω * ∏ ℓ ∈ eulerPrimes M f, (1 - ω (ℓ : ZMod f)) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  rw [sum_units_eq_sum (DirichletCharacter.changeLevel hfM ω) (fun x => sN M x.val),
    sum_zmod_eq_range, ← T_eq ω hfM hM]
  refine sum_congr rfl (fun i hi => ?_)
  have hi' := mem_range.1 hi
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hi']
  congr 1
  by_cases hc : i.Coprime M
  · rw [if_pos hc]
    have hu : IsUnit (i : ZMod M) := (ZMod.isUnit_iff_coprime i M).2 hc
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd ω hfM hu.unit
    rw [IsUnit.unit_spec] at this
    rw [this, ZMod.cast_natCast hfM]
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime i M).1 h))
end Erdos634.LemmaSC
end

section
open scoped BigOperators Topology ComplexConjugate Real
open Complex HurwitzZeta Filter
namespace Erdos634.LemmaSB1H
noncomputable def c (m : ℕ) (s : ℝ) : ℝ := ((m : ℝ) ^ s)⁻¹
theorem c_zero {s : ℝ} (hs : s ≠ 0) : c 0 s = 0 := by
  simp [c, Real.zero_rpow hs]
theorem c_one (s : ℝ) : c 1 s = 1 := by simp [c]
theorem c_diff_bound (n : ℕ) {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    0 ≤ c (n + 1) s - c (n + 2) s ∧ c (n + 1) s - c (n + 2) s ≤ 2 / ((n : ℝ) + 1) ^ 2 := by
  set m : ℝ := (n : ℝ) + 1 with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hm0 : 0 < m := by linarith
  have hcast1 : ((n + 1 : ℕ) : ℝ) = m := by push_cast; ring
  have hcast2 : ((n + 2 : ℕ) : ℝ) = m + 1 := by push_cast; ring
  unfold c
  rw [hcast1, hcast2]
  set q : ℝ := m / (m + 1) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by linarith)]; linarith
  have hsplit : ((m + 1) ^ s)⁻¹ = (m ^ s)⁻¹ * q ^ s := by
    rw [hq, Real.div_rpow hm0.le (by linarith)]
    have : (0 : ℝ) < (m + 1) ^ s := Real.rpow_pos_of_pos (by linarith) s
    have : (0 : ℝ) < m ^ s := Real.rpow_pos_of_pos hm0 s
    field_simp
  rw [hsplit]
  have hms : m ≤ m ^ s := by
    calc m = m ^ (1 : ℝ) := (Real.rpow_one m).symm
      _ ≤ m ^ s := Real.rpow_le_rpow_of_exponent_le hm1 h1
  have hinv : (m ^ s)⁻¹ ≤ m⁻¹ := inv_anti₀ hm0 hms
  have hinv0 : 0 ≤ (m ^ s)⁻¹ := inv_nonneg.mpr (Real.rpow_pos_of_pos hm0 s).le
  have hqs1 : q ^ s ≤ 1 := Real.rpow_le_one hq0.le hq1 (by linarith)
  have hqs2 : q ^ (2 : ℝ) ≤ q ^ s := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 h2
  rw [Real.rpow_two] at hqs2
  constructor
  · nlinarith
  · have e1 : (m ^ s)⁻¹ - (m ^ s)⁻¹ * q ^ s = (m ^ s)⁻¹ * (1 - q ^ s) := by ring
    rw [e1]
    have hb : 1 - q ^ s ≤ 1 - q ^ 2 := by linarith
    have hb0 : 0 ≤ 1 - q ^ s := by linarith
    calc (m ^ s)⁻¹ * (1 - q ^ s) ≤ m⁻¹ * (1 - q ^ 2) :=
          mul_le_mul hinv hb hb0 (inv_nonneg.mpr hm0.le)
      _ ≤ 2 / m ^ 2 := by
          rw [hq]
          have : m + 1 ≠ 0 := by linarith
          rw [div_pow, one_sub_div (by positivity), inv_mul_eq_div, div_div,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
noncomputable def F (w : ℂ) : ℂ := ∑' n : ℕ, w ^ (n + 2) / (((n : ℂ) + 1) * ((n : ℂ) + 2))
theorem hasSum_F {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => w ^ (n + 2) / (((n : ℂ) + 1) * ((n : ℂ) + 2)))
      ((1 - w) * log (1 - w) + w) := by
  have h1 := hasSum_taylorSeries_neg_log hw
  have h2 : HasSum (fun n : ℕ => w ^ (n + 1) / ((n : ℂ) + 1)) (-log (1 - w)) := by
    have := (hasSum_nat_add_iff' 1).mpr h1
    simpa using this
  have h3 : HasSum (fun n : ℕ => w ^ (n + 2) / ((n : ℂ) + 2)) (-log (1 - w) - w) := by
    have := (hasSum_nat_add_iff' 1).mpr h2
    have e1 : (fun n : ℕ => w ^ (n + 2) / ((n : ℂ) + 2))
        = (fun n : ℕ => w ^ (n + 1 + 1) / (((n + 1 : ℕ) : ℂ) + 1)) := by
      funext n; push_cast; ring_nf
    have e2 : -log (1 - w) - w
        = -log (1 - w) - ∑ i ∈ Finset.range 1, w ^ (i + 1) / ((i : ℂ) + 1) := by simp
    rw [e1, e2]; exact this
  have h4 := (h2.mul_left w).sub h3
  have e3 : (fun n : ℕ => w ^ (n + 2) / (((n : ℂ) + 1) * ((n : ℂ) + 2)))
      = (fun n : ℕ => w * (w ^ (n + 1) / ((n : ℂ) + 1)) - w ^ (n + 2) / ((n : ℂ) + 2)) := by
    funext n
    have a1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have a2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    field_simp
    ring
  have e4 : (1 - w) * log (1 - w) + w = w * -log (1 - w) - (-log (1 - w) - w) := by ring
  rw [e3, e4]; exact h4
theorem norm_F_term_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖w ^ (n + 2) / (((n : ℂ) + 1) * ((n : ℂ) + 2))‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  rw [norm_div, norm_pow, norm_mul]
  have e1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
  have e2 : ‖(n : ℂ) + 2‖ = (n : ℝ) + 2 := by exact_mod_cast Complex.norm_natCast (n + 2)
  rw [e1, e2]
  have hp : ‖w‖ ^ (n + 2) ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_nonneg (norm_nonneg w) (n + 2)]
theorem summable_bound : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this
theorem continuousOn_F : ContinuousOn F (Metric.closedBall 0 1) := by
  refine continuousOn_tsum (u := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (fun n => ?_) summable_bound
    (fun n w hw => norm_F_term_le (by simpa using hw) n)
  exact ((continuous_pow _).div_const _).continuousOn
theorem slit_of {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : 0 < (1 - z).re := by
  rw [sub_re, one_re, sub_pos]
  by_contra h
  push_neg at h
  have hre : z.re ≤ 1 := (Complex.re_le_norm z).trans hz.le
  have hre1 : z.re = 1 := le_antisymm hre h
  have hsq := Complex.sq_norm z
  rw [hz, Complex.normSq_apply, hre1] at hsq
  have him : z.im = 0 := by nlinarith
  exact hz1 (Complex.ext (by simp [hre1]) (by simp [him]))
theorem F_boundary {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    F z = (1 - z) * log (1 - z) + z := by
  have hslit : 1 - z ∈ slitPlane := Or.inl (slit_of hz hz1)
  have hpath : Tendsto (fun r : ℝ => (r : ℂ) * z) (𝓝[<] 1) (𝓝 z) := by
    have : Tendsto (fun r : ℝ => (r : ℂ) * z) (𝓝 1) (𝓝 ((1 : ℝ) * z)) :=
      ((continuous_ofReal.mul continuous_const).tendsto 1)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 := by
    have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [this] with r hr using hr
  have hnorm : ∀ r : ℝ, 0 < r → r < 1 → ‖(r : ℂ) * z‖ < 1 := fun r h0 h1 => by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]; exact h1
  have hF1 : Tendsto (fun r : ℝ => F ((r : ℂ) * z)) (𝓝[<] 1) (𝓝 (F z)) := by
    have hcw : ContinuousWithinAt F (Metric.closedBall 0 1) z :=
      continuousOn_F z (by simp [hz])
    refine hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hpath, ?_⟩)
    filter_upwards [hev] with r hr
    simpa using (hnorm r hr.1 hr.2).le
  have hG : ContinuousAt (fun w : ℂ => (1 - w) * log (1 - w) + w) z := by
    have hlog : ContinuousAt (fun w : ℂ => log (1 - w)) z :=
      (continuousAt_clog hslit).comp (continuous_const.sub continuous_id).continuousAt
    exact ((continuous_const.sub continuous_id).continuousAt.mul hlog).add continuousAt_id
  have hF2 : Tendsto (fun r : ℝ => F ((r : ℂ) * z)) (𝓝[<] 1)
      (𝓝 ((1 - z) * log (1 - z) + z)) := by
    refine (hG.tendsto.comp hpath).congr' ?_
    filter_upwards [hev] with r hr
    exact ((hasSum_F (hnorm r hr.1 hr.2)).tsum_eq).symm
  exact tendsto_nhds_unique hF1 hF2
noncomputable def D (z : ℂ) (s : ℝ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 2) * ((c (n + 1) s - c (n + 2) s : ℝ) : ℂ)
theorem D_one (z : ℂ) : D z 1 = F z := by
  unfold D F
  congr 1; funext n
  simp only [c, Real.rpow_one]
  have a1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have a2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  push_cast
  field_simp
  ring
theorem D_tendsto {z : ℂ} (hz : ‖z‖ = 1) : Tendsto (D z) (𝓝[>] 1) (𝓝 (D z 1)) := by
  unfold D
  have hbound : Summable (fun n : ℕ => 2 / ((n : ℝ) + 1) ^ 2) := by
    exact (summable_bound.mul_left 2).congr (fun n => by ring)
  refine tendsto_tsum_of_dominated_convergence hbound (fun n => ?_) ?_
  · 
    have hc : ∀ m : ℕ, 0 < m → Continuous (fun s : ℝ => c m s) := fun m hm => by
      unfold c
      refine Continuous.inv₀ (Real.continuous_const_rpow (by positivity)) fun s => ?_
      exact (Real.rpow_pos_of_pos (by exact_mod_cast hm) s).ne'
    have : Continuous (fun s : ℝ => z ^ (n + 2) * ((c (n + 1) s - c (n + 2) s : ℝ) : ℂ)) :=
      continuous_const.mul (continuous_ofReal.comp ((hc _ (by omega)).sub (hc _ (by omega))))
    exact (this.tendsto 1).mono_left nhdsWithin_le_nhds
  · have : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with s hs n
    obtain ⟨b0, b1⟩ := c_diff_bound n hs.1.le hs.2.le
    rw [norm_mul, norm_pow, hz, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg b0]
    exact b1
theorem hasSum_expZeta_c (y : ℝ) {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => cexp (2 * π * I * y) ^ n * (c n s : ℂ)) (expZeta y s) := by
  have h := hasSum_expZeta_of_one_lt_re y (s := (s : ℂ)) (by simpa using hs)
  convert h using 1
  funext n
  rw [← Complex.exp_nat_mul, c, ofReal_inv, ← div_eq_mul_inv]
  congr 1
  · ring_nf
  · rw [ofReal_cpow (Nat.cast_nonneg n)]; simp
theorem expZeta_eq_D (y : ℝ) {s : ℝ} (hs : 1 < s) (hz1 : cexp (2 * π * I * y) ≠ 1) :
    expZeta y s = (D (cexp (2 * π * I * y)) s - cexp (2 * π * I * y)) /
      (cexp (2 * π * I * y) - 1) := by
  set z := cexp (2 * π * I * y) with hzdef
  set S := expZeta y s
  have h0 := hasSum_expZeta_c y hs
  rw [← hzdef] at h0
  have hs0 : s ≠ 0 := by linarith
  have hA : HasSum (fun n : ℕ => z ^ (n + 1) * (c (n + 1) s : ℂ)) S := by
    have := (hasSum_nat_add_iff' 1).mpr h0
    simpa [c_zero hs0] using this
  have hB : HasSum (fun n : ℕ => z ^ (n + 2) * (c (n + 2) s : ℂ)) (S - z) := by
    have := (hasSum_nat_add_iff' 1).mpr hA
    simpa [c_one] using this
  have hC : HasSum (fun n : ℕ => z ^ (n + 2) * ((c (n + 1) s - c (n + 2) s : ℝ) : ℂ))
      (z * S - (S - z)) := by
    have := (hA.mul_left z).sub hB
    convert this using 1 <;> first | rfl | (funext n; push_cast; ring)
  have hD : D z s = z * S - (S - z) := hC.tsum_eq
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [hD]; field_simp; ring
theorem expZeta_one (y : ℝ) (hy : (y : UnitAddCircle) ≠ 0) (hz1 : cexp (2 * π * I * y) ≠ 1) :
    expZeta y 1 = -log (1 - cexp (2 * π * I * y)) := by
  set z := cexp (2 * π * I * y) with hzdef
  have hz : ‖z‖ = 1 := by
    rw [hzdef, show 2 * π * I * y = ((2 * π * y : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hcont : Tendsto (fun s : ℝ => expZeta y s) (𝓝[>] 1) (𝓝 (expZeta y 1)) := by
    have hc := (differentiableAt_expZeta (y : UnitAddCircle) 1 (Or.inr hy)).continuousAt
    have : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 1) (𝓝 (1 : ℂ)) := by
      simpa using (continuous_ofReal.tendsto (1 : ℝ))
    exact (hc.tendsto.comp this).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => expZeta y s) (𝓝[>] 1) (𝓝 ((D z 1 - z) / (z - 1))) := by
    refine (((D_tendsto hz).sub_const z).div_const (z - 1)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (expZeta_eq_D y hs hz1).symm
  rw [tendsto_nhds_unique hcont hlim, D_one, F_boundary hz hz1]
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp
  ring
theorem not_int_facts {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ((x : UnitAddCircle) ≠ 0) ∧ (((-x : ℝ) : UnitAddCircle) ≠ 0) ∧
      cexp (2 * π * I * x) ≠ 1 ∧ cexp (2 * π * I * ((-x : ℝ) : ℂ)) ≠ 1 := by
  have hint : ∀ n : ℤ, (n : ℝ) ≠ x := fun n hn => by
    have a : (0 : ℝ) < n := hn ▸ h0
    have b : (n : ℝ) < 1 := hn ▸ h1
    have a' : 0 < n := by exact_mod_cast a
    have b' : n < 1 := by exact_mod_cast b
    omega
  have hcirc : ∀ t : ℝ, (∀ n : ℤ, (n : ℝ) ≠ t) → (t : UnitAddCircle) ≠ 0 := fun t ht h => by
    rw [AddCircle.coe_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    exact ht n (by simpa using hn)
  have hexp : ∀ t : ℝ, (∀ n : ℤ, (n : ℝ) ≠ t) → cexp (2 * π * I * t) ≠ 1 := fun t ht h => by
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have : (t : ℂ) = n := by
      have := hn; rw [show (n : ℂ) * (2 * π * I) = 2 * π * I * n by ring] at this
      exact mul_left_cancel₀ hπ this
    exact ht n (by exact_mod_cast this.symm)
  have hint' : ∀ n : ℤ, (n : ℝ) ≠ -x := fun n hn => hint (-n) (by push_cast; linarith)
  exact ⟨hcirc x hint, hcirc (-x) hint', hexp x hint, hexp (-x) hint'⟩
theorem arg_one_sub_exp {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    arg (1 - cexp (2 * π * I * x)) = π * x - π / 2 := by
  set θ : ℝ := π * x - π / 2
  have hsin : 0 < Real.sin (π * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have key : 1 - cexp (2 * π * I * x) =
      ((2 * Real.sin (π * x) : ℝ) : ℂ) * (cos θ + sin θ * I) := by
    have hz : cexp (2 * π * I * x) = ((Real.cos (2 * π * x) : ℝ) : ℂ) +
        ((Real.sin (2 * π * x) : ℝ) : ℂ) * I := by
      rw [show 2 * π * I * x = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
        ← ofReal_cos, ← ofReal_sin]
    have hθ : cos (θ : ℂ) + sin (θ : ℂ) * I = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I := by
      rw [ofReal_cos, ofReal_sin]
    have hc : Real.cos θ = Real.sin (π * x) := by simp [θ, Real.cos_sub_pi_div_two]
    have hs : Real.sin θ = -Real.cos (π * x) := by simp [θ, Real.sin_sub_pi_div_two]
    have hc2 : Real.cos (2 * π * x) = 1 - 2 * Real.sin (π * x) ^ 2 := by
      rw [show 2 * π * x = 2 * (π * x) by ring, Real.cos_two_mul, Real.cos_sq']; ring
    have hs2 : Real.sin (2 * π * x) = 2 * Real.sin (π * x) * Real.cos (π * x) := by
      rw [show 2 * π * x = 2 * (π * x) by ring, Real.sin_two_mul]
    rw [hz, hθ, hc, hs, hc2, hs2]
    apply Complex.ext <;>
      simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_re, one_re, add_im, mul_im,
        sub_im, one_im] <;> ring
  rw [key, arg_real_mul _ (by positivity)]
  apply arg_cos_add_sin_mul_I
  constructor <;> simp only [θ] <;>
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos h0, mul_lt_mul_of_pos_left h1 Real.pi_pos]
theorem hurwitzOddZero : Erdos634.LemmaSB1.HurwitzOddZero := by
  intro x h0 h1
  obtain ⟨hx0, hmx0, hz1, hw1⟩ := not_int_facts h0 h1
  have hfe := hurwitzZetaOdd_one_sub (x : UnitAddCircle) (s := 1) (fun n h => by
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  rw [sub_self, cpow_neg_one, Complex.Gamma_one, mul_one, mul_div_assoc,
    show (π : ℂ) * (1 / 2) = π / 2 by ring, Complex.sin_pi_div_two, mul_one] at hfe
  rw [hfe]
  rw [sinZeta_eq, ← AddCircle.coe_neg, expZeta_one x hx0 hz1, expZeta_one (-x) hmx0 hw1]
  set z := cexp (2 * π * I * x) with hzdef
  have hw : cexp (2 * π * I * ((-x : ℝ) : ℂ)) = conj z := by
    rw [hzdef, ← Complex.exp_conj]; congr 1
    simp only [map_mul, map_ofNat, conj_ofReal, conj_I, ofReal_neg]; ring
  rw [hw, show (1 : ℂ) - conj z = conj (1 - z) by simp]
  have hz : ‖z‖ = 1 := by
    rw [hzdef, show 2 * π * I * x = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hre := slit_of hz hz1
  have hargpi : (1 - z).arg ≠ π := fun h => by
    have := (Complex.arg_eq_pi_iff.mp h).1; linarith
  rw [log_conj _ hargpi]
  set L := log (1 - z)
  have him : L.im = π * x - π / 2 := by rw [log_im]; exact arg_one_sub_exp h0 h1
  have hL : L = L.re + L.im * I := (Complex.re_add_im L).symm
  have hcL : conj L = L.re - L.im * I := by
    apply Complex.ext <;> simp
  rw [hcL, hL, him]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  push_cast
  ring_nf
  simp
  ring
theorem B1 {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (ho : χ.Odd) :
    ∑ j : ZMod N, χ j * ((Erdos634.LemmaS.saw ((j.val : ℚ) / N) : ℚ) : ℂ) ≠ 0 :=
  Erdos634.LemmaSB1.B1_of_hurwitzOddZero hurwitzOddZero hp ho
end Erdos634.LemmaSB1H
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSC
open Erdos634.LemmaS (saw)
instance conductor_neZero {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩
theorem sN_congr {M x y : ℕ} (h : (x : ZMod M) = (y : ZMod M)) : sN M x = sN M y := by
  rw [sN_mod, (ZMod.natCast_eq_natCast_iff' x y M).1 h, ← sN_mod]
theorem sum_comp_surj {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq H]
    (π : G →* H) (hπ : Function.Surjective π) (F : H → ℂ) :
    ∑ g, F (π g) = ((Finset.univ.filter (fun g => π g = 1)).card : ℂ) * ∑ h, F h := by
  rw [← Finset.sum_fiberwise Finset.univ π (fun g => F (π g)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.sum_congr rfl (fun g hg => congrArg F (Finset.mem_filter.1 hg).2), Finset.sum_const,
    nsmul_eq_mul]
  obtain ⟨g0, rfl⟩ := hπ h
  rw [MonoidHom.card_fiber_eq_of_mem_range π ⟨g0, rfl⟩ ⟨1, map_one π⟩]
theorem fiber_card {n d : ℕ} [NeZero n] [NeZero d] (hd : d ∣ n) :
    (((Finset.univ.filter (fun g => ZMod.unitsMap hd g = 1)).card : ℕ) : ℂ)
      = (n.totient : ℂ) / d.totient := by
  have h := sum_comp_surj (ZMod.unitsMap hd) (ZMod.unitsMap_surjective hd) (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ZMod.card_units_eq_totient] at h
  have hφ : (d.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))).ne'
  rw [eq_div_iff hφ, ← h]
theorem lemmaC {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) :
    ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * ((saw ((((k : ZMod n).val * a : ℕ) : ℚ) / n) : ℚ) : ℂ)
      = if χ.conductor ∣ n / n.gcd a then
          ((n.totient : ℂ) / (n / n.gcd a).totient)
            * χ.primitiveCharacter ((a / n.gcd a : ℕ) : ZMod χ.conductor)
            * B χ.primitiveCharacter⁻¹
            * ∏ ℓ ∈ eulerPrimes (n / n.gcd a) χ.conductor,
                (1 - χ.primitiveCharacter⁻¹ (ℓ : ZMod χ.conductor))
        else 0 := by
  set g := n.gcd a with hg
  set nx := n / g with hnxdef
  set b := a / g with hbdef
  set f := χ.conductor with hfdef
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left a hn
  have hn_eq : n = g * nx := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n a)).symm
  have ha_eq : a = g * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n a)).symm
  have hnx0 : 0 < nx := Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_left n a)) hg0
  haveI : NeZero nx := ⟨hnx0.ne'⟩
  have hnx : nx ∣ n := ⟨g, by rw [hn_eq, mul_comm]⟩
  have hcop : b.Coprime nx := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := n) (by rw [Nat.gcd_comm]; exact hg0)
    rw [Nat.gcd_comm] at this; exact this
  set π := ZMod.unitsMap hnx with hπ
  set H : (ZMod nx)ˣ → ℂ := fun u => sN nx ((u : ZMod nx).val * b) with hH
  have step1 : ∀ k : (ZMod n)ˣ,
      ((saw ((((k : ZMod n).val * a : ℕ) : ℚ) / n) : ℚ) : ℂ) = H (π k) := by
    intro k
    change sN n ((k : ZMod n).val * a) = sN nx (((π k : (ZMod nx)ˣ) : ZMod nx).val * b)
    have e1 : sN n ((k : ZMod n).val * a) = sN nx ((k : ZMod n).val * b) := by
      have h1 := sN_mul hg0 nx ((k : ZMod n).val * b)
      rw [← hn_eq] at h1
      rw [show (k : ZMod n).val * a = g * ((k : ZMod n).val * b) by rw [ha_eq]; ring]
      exact h1
    rw [e1]
    apply sN_congr
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
    push_cast
    rw [ZMod.natCast_zmod_val]
  simp_rw [step1]
  by_cases hdiv : f ∣ nx
  · 
    rw [if_pos hdiv]
    set χs := χ.primitiveCharacter with hχs
    set χ₁ := DirichletCharacter.changeLevel hdiv χs with hχ₁
    have hχ : χ = DirichletCharacter.changeLevel hnx χ₁ := by
      rw [hχ₁, ← DirichletCharacter.changeLevel_trans]
      exact (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
    have hval : ∀ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) = χ₁⁻¹ ((π k : (ZMod nx)ˣ) : ZMod nx) := by
      intro k
      rw [hχ, ← map_inv, DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]
    simp_rw [hval]
    rw [sum_comp_surj π (ZMod.unitsMap_surjective hnx) (fun u => χ₁⁻¹ (u : ZMod nx) * H u),
      fiber_card hnx]
    set β : (ZMod nx)ˣ := ZMod.unitOfCoprime b hcop with hβ
    have hβv : (β : ZMod nx) = (b : ZMod nx) := ZMod.coe_unitOfCoprime b hcop
    have hsub : ∑ u : (ZMod nx)ˣ, χ₁⁻¹ (u : ZMod nx) * H u
        = χ₁ (β : ZMod nx) * ∑ v : (ZMod nx)ˣ, χ₁⁻¹ (v : ZMod nx) * sN nx (v : ZMod nx).val := by
      rw [← Equiv.sum_comp (Equiv.mulRight β⁻¹), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      simp only [Equiv.coe_mulRight, Units.val_mul]
      have hH' : H (v * β⁻¹) = sN nx (v : ZMod nx).val := by
        change sN nx (((v * β⁻¹ : (ZMod nx)ˣ) : ZMod nx).val * b) = _
        apply sN_congr
        push_cast
        simp only [ZMod.natCast_zmod_val, ← hβv, Units.val_mul, Units.inv_mul_cancel_right]
      have hinv : χ₁⁻¹ ((β⁻¹ : (ZMod nx)ˣ) : ZMod nx) = χ₁ (β : ZMod nx) := by
        rw [MulChar.inv_apply, Ring.inverse_unit, inv_inv]
      rw [map_mul, hH', hinv]; ring
    rw [hsub]
    have hω : χ₁⁻¹ = DirichletCharacter.changeLevel hdiv χs⁻¹ := by rw [hχ₁, map_inv]
    have hT := sum_units_changeLevel χs⁻¹ hdiv
    rw [← hω] at hT
    rw [hT]
    have hb : χ₁ (β : ZMod nx) = χs ((b : ℕ) : ZMod f) := by
      rw [hχ₁, DirichletCharacter.changeLevel_eq_cast_of_dvd, hβv, ZMod.cast_natCast hdiv]
    rw [hb]; ring
  · 
    rw [if_neg hdiv]
    have hnot : ¬ DirichletCharacter.FactorsThrough χ nx := by
      intro h
      exact hdiv ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hnx).1 h)
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) hnx] at hnot
    obtain ⟨k0, hk0, hk0'⟩ := SetLike.not_le_iff_exists.1 hnot
    have hk0π : π k0 = 1 := hk0
    have hχk0 : χ (k0 : ZMod n) ≠ 1 := by
      intro h; apply hk0'
      change χ.toUnitHom k0 = 1
      exact Units.ext (by rw [MulChar.coe_toUnitHom, h]; rfl)
    have hprod : χ⁻¹ (k0 : ZMod n) * χ (k0 : ZMod n) = 1 := by
      have h2 : (χ⁻¹ * χ) (k0 : ZMod n) = χ⁻¹ (k0 : ZMod n) * χ (k0 : ZMod n) := rfl
      rw [← h2, inv_mul_cancel, MulChar.one_apply_coe]
    have hne : χ⁻¹ (k0 : ZMod n) ≠ 1 := by
      intro h; rw [h, one_mul] at hprod; exact hχk0 hprod
    set S := ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * H (π k) with hS
    have hSS : S = χ⁻¹ (k0 : ZMod n) * S := by
      rw [hS]
      conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft k0)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Equiv.coe_mulLeft, Units.val_mul, map_mul, hk0π, one_mul]
      ring
    have : (1 - χ⁻¹ (k0 : ZMod n)) * S = 0 := by rw [sub_mul, one_mul, ← hSS, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h
end Erdos634.LemmaSC
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSC
open Erdos634.LemmaS (saw relSpace mem_relSpace)
theorem saw_neg (t : ℚ) : saw (-t) = -saw t := by
  unfold saw
  by_cases h : Int.fract t = 0
  · rw [if_pos (Int.fract_neg_eq_zero.2 h), if_pos h, neg_zero]
  · rw [if_neg (fun h' => h (Int.fract_neg_eq_zero.1 h')), if_neg h, Int.fract_neg h]
    ring
theorem sN_neg {M x y : ℕ} (hM : 0 < M) (h : M ∣ x + y) : sN M y = -sN M x := by
  obtain ⟨m, hm⟩ := h
  unfold sN
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hy : (y : ℚ) / M = -((x : ℚ) / M) + (m : ℕ) := by
    have : (y : ℚ) = M * m - x := by
      have h2 : ((x + y : ℕ) : ℚ) = ((M * m : ℕ) : ℚ) := by rw [hm]
      push_cast at h2; linarith
    rw [this]; field_simp; ring
  rw [hy, saw_add_nat, saw_neg]
  push_cast; ring
theorem fourier_zero {n : ℕ} [NeZero n] (F : (ZMod n)ˣ → ℂ)
    (h : ∀ χ : DirichletCharacter ℂ n, ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * F k = 0)
    (k0 : (ZMod n)ˣ) : F k0 = 0 := by
  have h1 : ∑ χ : DirichletCharacter ℂ n, χ (k0 : ZMod n) *
      ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * F k = 0 := by simp [h]
  simp_rw [mul_sum] at h1
  rw [sum_comm] at h1
  have h2 : ∀ k : (ZMod n)ˣ, ∑ χ : DirichletCharacter ℂ n, χ (k0 : ZMod n) * (χ⁻¹ (k : ZMod n) * F k)
      = (if (k : ZMod n) = k0 then (n.totient : ℂ) else 0) * F k := by
    intro k
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit k) (k0 : ZMod n), sum_mul]
    refine sum_congr rfl (fun χ _ => ?_)
    rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    ring
  rw [sum_congr rfl (fun k _ => h2 k)] at h1
  simp_rw [Units.val_inj] at h1
  rw [sum_eq_single k0 (fun k _ hk => by rw [if_neg hk, zero_mul])
    (fun h => absurd (mem_univ k0) h), if_pos rfl] at h1
  have hφ : (n.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  exact (mul_eq_zero.1 h1).resolve_left hφ
noncomputable def bracket {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) : ℂ :=
  if χ.conductor ∣ n / n.gcd a then
    ((n.totient : ℂ) / (n / n.gcd a).totient)
      * χ.primitiveCharacter ((a / n.gcd a : ℕ) : ZMod χ.conductor)
      * ∏ ℓ ∈ eulerPrimes (n / n.gcd a) χ.conductor,
          (1 - χ.primitiveCharacter⁻¹ (ℓ : ZMod χ.conductor))
  else 0
noncomputable def LHSC {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) : ℂ :=
  ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * sN n ((k : ZMod n).val * a)
theorem LHSC_eq {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) :
    LHSC χ a = B χ.primitiveCharacter⁻¹ * bracket χ a := by
  have := lemmaC χ a
  unfold LHSC bracket
  change ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * ((saw ((((k : ZMod n).val * a : ℕ) : ℚ) / n) : ℚ) : ℂ) = _
  rw [this]
  split_ifs <;> ring
theorem primitiveCharacter_odd {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (ho : χ.Odd) :
    χ.primitiveCharacter.Odd := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter
    χ.conductor_dvd_level (-1)
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  simp only [Units.val_neg, Units.val_one] at h
  rw [ZMod.cast_neg χ.conductor_dvd_level, ZMod.cast_one χ.conductor_dvd_level] at h
  show χ.primitiveCharacter (-1) = -1
  rw [← h]; exact ho
theorem B_ne_zero {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (ho : χ.Odd) :
    B χ.primitiveCharacter⁻¹ ≠ 0 := by
  have hp : (χ.primitiveCharacter⁻¹).IsPrimitive := by
    show (χ.primitiveCharacter⁻¹).conductor = χ.conductor
    rw [DirichletCharacter.conductor_inv]
    exact DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hodd : (χ.primitiveCharacter⁻¹).Odd :=
    Erdos634.LemmaSB1.inv_odd (primitiveCharacter_odd ho)
  exact Erdos634.LemmaSB1H.B1 hp hodd
theorem even_sum_zero {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (he : χ.Even) (a : ℕ) :
    LHSC χ a = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hinv : ∀ k : (ZMod n)ˣ, χ⁻¹ ((-k : (ZMod n)ˣ) : ZMod n) = χ⁻¹ (k : ZMod n) := by
    intro k
    have hev : χ (-(k : ZMod n)) = χ (k : ZMod n) := DirichletCharacter.Even.to_fun he (k : ZMod n)
    rw [Units.val_neg, MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hev]
  have hs : ∀ k : (ZMod n)ˣ, sN n (((-k : (ZMod n)ˣ) : ZMod n).val * a)
      = -sN n ((k : ZMod n).val * a) := by
    intro k
    apply sN_neg hn
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simp only [ZMod.natCast_zmod_val, Units.val_neg]; ring
  set S := LHSC χ a with hS
  have hSS : S = -S := by
    rw [hS]; unfold LHSC
    conv_lhs => rw [← Equiv.sum_comp (Equiv.neg (ZMod n)ˣ)]
    rw [← sum_neg_distrib]
    refine sum_congr rfl (fun k _ => ?_)
    simp only [Equiv.neg_apply, hinv, hs]; ring
  have : (2 : ℂ) * S = 0 := by linear_combination hSS
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero
theorem key_sum {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) :
    ∑ i, (e i : ℂ) * LHSC χ (a i)
      = ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * ∑ i, (e i : ℂ) * sN n ((k : ZMod n).val * a i) := by
  unfold LHSC
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun k _ => sum_congr rfl (fun i _ => by ring))
theorem inner_cast {n : ℕ} (k : ℕ) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) :
    (((∑ i, saw ((k * a i : ℕ) / (n : ℚ)) * e i : ℚ)) : ℂ) = ∑ i, (e i : ℂ) * sN n (k * a i) := by
  rw [Rat.cast_sum]
  refine sum_congr rfl (fun i _ => ?_)
  rw [Rat.cast_mul, mul_comm]; rfl
theorem mem_relSpace_iff_odd {n : ℕ} [NeZero n] (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) :
    e ∈ relSpace n a ↔
      ∀ χ : DirichletCharacter ℂ n, χ.Odd → ∑ i, (e i : ℂ) * bracket χ (a i) = 0 := by
  constructor
  · intro he χ ho
    have hin : ∀ k : (ZMod n)ˣ, ∑ i, (e i : ℂ) * sN n ((k : ZMod n).val * a i) = 0 := by
      intro k
      rw [← inner_cast, (mem_relSpace.1 he) _ (ZMod.val_coe_unit_coprime k), Rat.cast_zero]
    have h1 := key_sum χ a e
    simp only [hin, mul_zero, sum_const_zero, LHSC_eq] at h1
    have h2 : B χ.primitiveCharacter⁻¹ * ∑ i, (e i : ℂ) * bracket χ (a i) = 0 := by
      rw [mul_sum, ← h1]; refine sum_congr rfl (fun i _ => by ring)
    exact (mul_eq_zero.1 h2).resolve_left (B_ne_zero ho)
  · intro h
    set F : (ZMod n)ˣ → ℂ := fun k => ∑ i, (e i : ℂ) * sN n ((k : ZMod n).val * a i) with hF
    have hall : ∀ χ : DirichletCharacter ℂ n, ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * F k = 0 := by
      intro χ
      simp only [hF]
      rw [← key_sum]
      rcases χ.even_or_odd with he | ho
      · simp [even_sum_zero he]
      · simp_rw [LHSC_eq]
        have : ∑ i, (e i : ℂ) * (B χ.primitiveCharacter⁻¹ * bracket χ (a i))
            = B χ.primitiveCharacter⁻¹ * ∑ i, (e i : ℂ) * bracket χ (a i) := by
          rw [mul_sum]; exact sum_congr rfl (fun i _ => by ring)
        rw [this, h χ ho, mul_zero]
    rw [mem_relSpace]
    intro k hk
    have hF0 := fourier_zero F hall (ZMod.unitOfCoprime k hk)
    have : (((∑ i, saw ((k * a i : ℕ) / (n : ℚ)) * e i : ℚ)) : ℂ) = 0 := by
      rw [inner_cast, ← hF0]
      refine sum_congr rfl (fun i _ => ?_)
      congr 1
      apply sN_congr
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.coe_unitOfCoprime]
    exact_mod_cast this
end Erdos634.LemmaSC
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSN
theorem pred_dvd (p r : ℕ) : p ^ (r - 1) ∣ p ^ r := pow_dvd_pow p (Nat.sub_le r 1)
theorem isPrimitive_iff_not_factorsThrough {p r : ℕ} [hp : Fact p.Prime] (hr : 1 ≤ r)
    (ψ : DirichletCharacter ℂ (p ^ r)) :
    ψ.IsPrimitive ↔ ¬ ψ.FactorsThrough (p ^ (r - 1)) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hlt : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  constructor
  · intro hprim hf
    have h1 := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd ψ (pred_dvd p r)).1 hf
    rw [show ψ.conductor = p ^ r from hprim] at h1
    exact absurd (Nat.le_of_dvd (pow_pos hp.out.pos _) h1) (not_le.2 hlt)
  · intro hnf
    show ψ.conductor = p ^ r
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow hp.out).1 ψ.conductor_dvd_level
    by_contra hne
    have hir : i ≤ r - 1 := by
      rcases Nat.lt_or_ge i r with h | h
      · omega
      · exact absurd (by rw [hci, show i = r by omega]) hne
    apply hnf
    exact (DirichletCharacter.mem_conductorSet_iff_conductor_dvd ψ (pred_dvd p r)).2
      (by rw [hci]; exact pow_dvd_pow p hir)
theorem lemmaN {p r : ℕ} [hp : Fact p.Prime] (hr : 1 ≤ r) (Φ : (ZMod (p ^ r))ˣ → ℂ) {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0)
    (u n0 : (ZMod (p ^ r))ˣ) (hn0 : ZMod.unitsMap (pred_dvd p r) n0 = 1) :
    Φ (u * n0) + ε * Φ (-(u * n0)) = Φ u + ε * Φ (-u) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set Ψ : (ZMod (p ^ r))ˣ → ℂ := fun v => Φ v + ε * Φ (-v) with hΨ
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hann : ∀ ω : DirichletCharacter ℂ (p ^ r), ω.IsPrimitive →
      ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ v = 0 := by
    intro ω hω
    have hneg : ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Φ (-v)
        = ω (-1) * ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Φ v := by
      rw [← Equiv.sum_comp (Equiv.neg _), mul_sum]
      refine sum_congr rfl (fun v _ => ?_)
      simp only [Equiv.neg_apply, neg_neg, Units.val_neg]
      rw [neg_eq_neg_one_mul (v : ZMod (p ^ r)), map_mul]; ring
    have hsplit : ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ v
        = (1 + ε * ω (-1)) * ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Φ v := by
      simp only [hΨ, mul_add, sum_add_distrib]
      rw [show ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * (ε * Φ (-v))
          = ε * ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Φ (-v) by
            rw [mul_sum]; exact sum_congr rfl (fun v _ => by ring), hneg]
      ring
    rw [hsplit]
    by_cases hpar : ω (-1) = ε
    · rw [h ω hω hpar, mul_zero]
    · have hm : ω (-1) = -ε := by
        rcases ω.even_or_odd with h1 | h1 <;> rcases hε with rfl | rfl
        · exact absurd h1 hpar
        · exact (by rw [show ω (-1) = 1 from h1]; try norm_num)
        · exact (by rw [show ω (-1) = -1 from h1]; try norm_num)
        · exact absurd h1 hpar
      rw [hm, show 1 + ε * -ε = 1 - ε * ε by ring, hε2, sub_self, zero_mul]
  have hall : ∀ ψ : DirichletCharacter ℂ (p ^ r),
      ∑ v : (ZMod (p ^ r))ˣ, ψ⁻¹ (v : ZMod (p ^ r)) * (Ψ (v * n0) - Ψ v) = 0 := by
    intro ψ
    set ω := ψ⁻¹ with hωdef
    have hshift : ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ (v * n0)
        = ω ((n0⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) *
            ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ v := by
      rw [← Equiv.sum_comp (Equiv.mulRight n0⁻¹), mul_sum]
      refine sum_congr rfl (fun v _ => ?_)
      simp only [Equiv.coe_mulRight, Units.val_mul, map_mul, inv_mul_cancel_right]
      ring
    have hdiff : ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * (Ψ (v * n0) - Ψ v)
        = (ω ((n0⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) - 1) *
            ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ v := by
      rw [sub_mul, one_mul, ← hshift, ← sum_sub_distrib]
      exact sum_congr rfl (fun v _ => by ring)
    rw [hdiff]
    by_cases hω : ω.IsPrimitive
    · rw [hann ω hω, mul_zero]
    · have hf : ω.FactorsThrough (p ^ (r - 1)) :=
        not_not.1 (fun h' => hω ((isPrimitive_iff_not_factorsThrough hr ω).2 h'))
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := ω) (pred_dvd p r)] at hf
      have hmem : n0⁻¹ ∈ (ZMod.unitsMap (pred_dvd p r)).ker := by
        rw [MonoidHom.mem_ker, map_inv, hn0, inv_one]
      have h1 := hf hmem
      rw [MonoidHom.mem_ker] at h1
      have h2 : ω ((n0⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) = 1 := by
        rw [← MulChar.coe_toUnitHom, h1, Units.val_one]
      rw [h2, sub_self, zero_mul]
  have := Erdos634.LemmaSC.fourier_zero (fun v => Ψ (v * n0) - Ψ v) hall u
  simp only [hΨ] at this
  linear_combination this
theorem lemmaN_a {p r : ℕ} [hp : Fact p.Prime] (hr : 1 ≤ r) (Φ : (ZMod (p ^ r))ˣ → ℂ) {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0)
    (hcount : ∀ u : (ZMod (p ^ r))ˣ,
      (univ.filter (fun v => ZMod.unitsMap (pred_dvd p r) v = ZMod.unitsMap (pred_dvd p r) u ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0))).card
        < (univ.filter (fun v => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    ∀ u, Φ u = -ε * Φ (-u) := by
  intro u
  by_contra hne
  have hΨ : Φ u + ε * Φ (-u) ≠ 0 := fun h0 => hne (by linear_combination h0)
  apply absurd (hcount u)
  apply not_lt.2
  apply Finset.card_le_card_of_injOn (fun n => u * n)
  · intro n hn
    have hn' := (mem_filter.1 hn).2
    refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
    · rw [map_mul, hn', mul_one]
    · have hinv := lemmaN hr Φ hε h u n hn'
      by_contra hboth
      push Not at hboth
      apply hΨ
      rw [← hinv, hboth.1, hboth.2, mul_zero, add_zero]
  · intro x _ y _ hxy
    exact mul_left_cancel hxy
theorem unitsMap_one_trivial {p : ℕ} (n0 : (ZMod (p ^ 1))ˣ) : ZMod.unitsMap (pred_dvd p 1) n0 = 1 := by
  apply Units.ext
  show (_ : ZMod 1) = _
  exact Subsingleton.elim _ _
theorem lemmaN_b {p : ℕ} [hp : Fact p.Prime] (Φ : (ZMod (p ^ 1))ˣ → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (p ^ 1))ˣ, ψ (u : ZMod (p ^ 1)) * Φ u = 0) :
    ∀ u, Φ u = Φ (-u) := by
  intro u
  have h1 := lemmaN le_rfl Φ (Or.inr rfl) h u (-1) (unitsMap_one_trivial _)
  rw [mul_neg_one, neg_neg] at h1
  linear_combination (-1/2 : ℂ) * h1
theorem lemmaN_c_const {p : ℕ} [hp : Fact p.Prime] (Φ : (ZMod (p ^ 1))ˣ → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (p ^ 1))ˣ, ψ (u : ZMod (p ^ 1)) * Φ u = 0) :
    ∀ u, Φ u + Φ (-u) = Φ 1 + Φ (-1) := by
  intro u
  have h1 := lemmaN le_rfl Φ (Or.inl rfl) h 1 u (unitsMap_one_trivial _)
  rw [one_mul, one_mul] at h1
  linear_combination h1
theorem lemmaN_c {p : ℕ} [hp : Fact p.Prime] (Φ : (ZMod (p ^ 1))ˣ → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (p ^ 1))ˣ, ψ (u : ZMod (p ^ 1)) * Φ u = 0)
    (hcard : (univ.filter (fun v : (ZMod (p ^ 1))ˣ => Φ v + Φ (-v) ≠ 0)).card < p - 1) :
    ∀ u, Φ u = -Φ (-u) := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hc := lemmaN_c_const Φ h
  have hzero : Φ 1 + Φ (-1) = 0 := by
    by_contra hne
    have hall : univ.filter (fun v : (ZMod (p ^ 1))ˣ => Φ v + Φ (-v) ≠ 0) = univ := by
      ext v; simp only [mem_filter, mem_univ, true_and, iff_true]; rw [hc v]; exact hne
    rw [hall, card_univ, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp.out] at hcard
    exact lt_irrefl _ hcard
  intro u
  have := hc u
  rw [hzero] at this
  linear_combination this
end Erdos634.LemmaSN
end

section
open scoped BigOperators
open Finset
open scoped Classical
namespace Erdos634.LemmaSGpp
open Erdos634.LemmaSN (pred_dvd isPrimitive_iff_not_factorsThrough)
def SpPP (q k : ℕ) (z : ℤ) : Prop :=
  z ≡ 1 [ZMOD (q : ℤ) ^ k] ∨ (q = 3 ∧ k = 1 ∧ z ≡ -1 [ZMOD 3]) ∨
    (q = 2 ∧ 2 ≤ k ∧ z ≡ 1 + 2 ^ (k - 1) [ZMOD 2 ^ k])
section PP
variable {q v : ℕ} [hq : Fact q.Prime]
theorem sum_prim (hv : 1 ≤ v) (g : (ZMod (q ^ v))ˣ) :
    ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive), χ (g : ZMod (q ^ v))
      = (if (g : ZMod (q ^ v)) = 1 then (((q ^ v).totient : ℕ) : ℂ) else 0) -
        (if ((g : ZMod (q ^ v)).cast : ZMod (q ^ (v - 1))) = 1
          then (((q ^ (v - 1)).totient : ℕ) : ℂ) else 0) := by
  classical
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  haveI : NeZero (q ^ (v - 1)) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  have hd := pred_dvd q v
  have hall := DirichletCharacter.sum_characters_eq ℂ (g : ZMod (q ^ v))
  have hall' := DirichletCharacter.sum_characters_eq ℂ
    (((g : ZMod (q ^ v)).cast : ZMod (q ^ (v - 1))))
  rw [← sum_filter_add_sum_filter_not univ (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)]
    at hall
  have hY : univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => ¬ χ.IsPrimitive)
      = univ.map ⟨DirichletCharacter.changeLevel hd, DirichletCharacter.changeLevel_injective hd⟩ := by
    ext ψ
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hnp
      have hf : ψ.FactorsThrough (q ^ (v - 1)) :=
        not_not.1 (fun h' => hnp ((isPrimitive_iff_not_factorsThrough hv ψ).2 h'))
      exact ⟨hf.χ₀, hf.eq_changeLevel.symm⟩
    · rintro ⟨ψ', rfl⟩ hprim
      exact (isPrimitive_iff_not_factorsThrough hv _).1 hprim ⟨hd, ψ', rfl⟩
  rw [hY, sum_map] at hall
  simp only [Function.Embedding.coeFn_mk, DirichletCharacter.changeLevel_eq_cast_of_dvd] at hall
  rw [hall'] at hall
  linear_combination hall
theorem totient_lt (hv : 1 ≤ v) (h2 : q ^ v ≠ 2) : (q ^ (v - 1)).totient < (q ^ v).totient := by
  have hq2 := hq.out.two_le
  rcases Nat.lt_or_ge v 2 with h | h
  · obtain rfl : v = 1 := by omega
    simp only [pow_one, Nat.sub_self, pow_zero, Nat.totient_one] at h2 ⊢
    rw [Nat.totient_prime hq.out]; omega
  · have htot : (q ^ v).totient = q * (q ^ (v - 1)).totient := by
      rw [show q ^ v = q * q ^ (v - 1) by rw [← pow_succ']; congr 1; omega]
      exact Nat.totient_mul_of_prime_of_dvd hq.out (dvd_pow_self q (by omega))
    have : 0 < (q ^ (v - 1)).totient := Nat.totient_pos.2 (by positivity)
    rw [htot]; nlinarith
theorem card_prim (hv : 1 ≤ v) :
    (univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)).card +
      (q ^ (v - 1)).totient = (q ^ v).totient := by
  classical
  have h := sum_prim hv (1 : (ZMod (q ^ v))ˣ)
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  rw [if_pos Units.val_one, if_pos (by rw [Units.val_one]; exact ZMod.cast_one (pred_dvd q v))] at h
  simp only [Units.val_one, MulChar.map_one, sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast (show (((univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)).card
    + (q ^ (v - 1)).totient : ℕ) : ℂ) = (q ^ v).totient by push_cast; rw [h]; ring)
theorem exists_primitive_pp (hv : 1 ≤ v) (h2 : q ^ v ≠ 2) :
    ∃ χ : DirichletCharacter ℂ (q ^ v), χ.IsPrimitive := by
  classical
  have hc := card_prim (q := q) hv
  have hl := totient_lt (q := q) hv h2
  obtain ⟨χ, hχ⟩ := card_pos.1 (show 0 < (univ.filter
    (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)).card by omega)
  exact ⟨χ, (mem_filter.1 hχ).2⟩
theorem all_neg_one {ι : Type*} (s : Finset ι) (w : ι → ℂ) (hn : ∀ i ∈ s, ‖w i‖ = 1)
    (hs : ∑ i ∈ s, w i = -(s.card : ℂ)) : ∀ i ∈ s, w i = -1 := by
  have hre : ∑ i ∈ s, (1 + (w i).re) = 0 := by
    have := congrArg Complex.re hs
    rw [Complex.re_sum] at this
    simp only [Complex.neg_re, Complex.natCast_re] at this
    rw [sum_add_distrib, this]; simp
  have hnn : ∀ i ∈ s, 0 ≤ 1 + (w i).re := by
    intro i hi
    have := Complex.abs_re_le_norm (w i)
    rw [hn i hi] at this
    linarith [neg_abs_le (w i).re]
  intro i hi
  have h1 := (sum_eq_zero_iff_of_nonneg hnn).1 hre i hi
  have hsq := Complex.sq_norm (w i)
  rw [hn i hi, Complex.normSq_apply] at hsq
  have hr : (w i).re = -1 := by linarith
  have him : (w i).im = 0 := by nlinarith
  exact Complex.ext (by simp [hr]) (by simp [him])
theorem lemmaGpp (hv : 1 ≤ v) (h2 : q ^ v ≠ 2) (g : (ZMod (q ^ v))ˣ) (z : ℤ)
    (hz : ((z : ℤ) : ZMod (q ^ v)) = g) :
    ((∃ c : ℂ, ∀ χ : DirichletCharacter ℂ (q ^ v), χ.IsPrimitive → χ (g : ZMod (q ^ v)) = c) ↔
      SpPP q v z) ∧
    (SpPP q v z → ∀ χ : DirichletCharacter ℂ (q ^ v), χ.IsPrimitive →
      χ (g : ZMod (q ^ v)) = if z ≡ 1 [ZMOD (q : ℤ) ^ v] then 1 else -1) := by
  classical
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  have hq2 := hq.out.two_le
  have hS := sum_prim hv g
  have hcard := card_prim (q := q) hv
  have hlt := totient_lt (q := q) hv h2
  set Pr := univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive) with hPr
  set T := (q ^ v).totient
  set D := (q ^ (v - 1)).totient
  have e1 : (g : ZMod (q ^ v)) = 1 ↔ z ≡ 1 [ZMOD (q : ℤ) ^ v] := by
    rw [← hz, ← Int.cast_one, ZMod.intCast_eq_intCast_iff]; push_cast; rfl
  have e0 : ((g : ZMod (q ^ v)).cast : ZMod (q ^ (v - 1))) = 1 ↔
      z ≡ 1 [ZMOD (q : ℤ) ^ (v - 1)] := by
    rw [← hz, ZMod.cast_intCast (pred_dvd q v), ← Int.cast_one, ZMod.intCast_eq_intCast_iff]
    push_cast; rfl
  have hT2 : T = 2 * D ↔ (q = 2 ∧ 2 ≤ v) ∨ (q = 3 ∧ v = 1) := by
    rcases Nat.lt_or_ge v 2 with h | h
    · obtain rfl : v = 1 := by omega
      show (q ^ 1).totient = 2 * (q ^ 0).totient ↔ _
      rw [pow_zero, pow_one, Nat.totient_one, Nat.totient_prime hq.out]
      omega
    · have htot : T = q * D := by
        simp only [T, D]
        rw [show q ^ v = q * q ^ (v - 1) by rw [← pow_succ']; congr 1; omega]
        exact Nat.totient_mul_of_prime_of_dvd hq.out (dvd_pow_self q (by omega))
      have : 0 < D := Nat.totient_pos.2 (by positivity)
      rw [htot]
      constructor
      · intro e; left; exact ⟨Nat.eq_of_mul_eq_mul_right this (by linarith), h⟩
      · rintro (⟨rfl, -⟩ | ⟨-, h'⟩)
        · rfl
        · omega
  have hnorm : ∀ χ ∈ Pr, ‖χ (g : ZMod (q ^ v))‖ = 1 := fun χ _ => χ.unit_norm_eq_one g
  have hexc : SpPP q v z → ¬ z ≡ 1 [ZMOD (q : ℤ) ^ v] →
      z ≡ 1 [ZMOD (q : ℤ) ^ (v - 1)] ∧ T = 2 * D := by
    rintro (h | ⟨rfl, rfl, h⟩ | ⟨rfl, hk, h⟩) hn
    · exact absurd h hn
    · exact ⟨by simp [Int.modEq_one], hT2.2 (Or.inr ⟨rfl, rfl⟩)⟩
    · refine ⟨?_, hT2.2 (Or.inl ⟨rfl, hk⟩)⟩
      have hp : (2 : ℤ) ^ v = 2 ^ (v - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      have hdv : (2 : ℤ) ^ (v - 1) ∣ 2 ^ v := ⟨2, hp⟩
      have h' := h.of_dvd hdv
      show z ≡ 1 [ZMOD ((2 : ℕ) : ℤ) ^ (v - 1)]
      push_cast
      refine h'.trans ?_
      rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
  have hval : SpPP q v z → ∀ χ : DirichletCharacter ℂ (q ^ v), χ.IsPrimitive →
      χ (g : ZMod (q ^ v)) = if z ≡ 1 [ZMOD (q : ℤ) ^ v] then 1 else -1 := by
    intro hsp χ hχ
    by_cases h1 : z ≡ 1 [ZMOD (q : ℤ) ^ v]
    · rw [if_pos h1, e1.2 h1, map_one]
    · rw [if_neg h1]
      obtain ⟨h0, hT⟩ := hexc hsp h1
      rw [if_neg (fun h => h1 (e1.1 h)), if_pos (e0.2 h0), zero_sub] at hS
      refine all_neg_one Pr _ hnorm ?_ χ (mem_filter.2 ⟨mem_univ _, hχ⟩)
      rw [hS]; congr 1; exact_mod_cast (show D = Pr.card by omega)
  refine ⟨⟨?_, ?_⟩, hval⟩
  · rintro ⟨c, hc⟩
    by_cases h1 : z ≡ 1 [ZMOD (q : ℤ) ^ v]
    · exact Or.inl h1
    obtain ⟨χ0, hχ0⟩ := card_pos.1 (show 0 < Pr.card by omega)
    have hcn : ‖c‖ = 1 := by rw [← hc χ0 (mem_filter.1 hχ0).2]; exact hnorm χ0 hχ0
    rw [sum_congr rfl (fun χ hχ => hc χ (mem_filter.1 hχ).2), sum_const, nsmul_eq_mul,
      if_neg (fun h => h1 (e1.1 h)), zero_sub] at hS
    by_cases h0 : z ≡ 1 [ZMOD (q : ℤ) ^ (v - 1)]
    · rw [if_pos (e0.2 h0)] at hS
      have hPD : Pr.card = D := by
        have := congrArg norm hS
        rw [norm_mul, hcn, mul_one, norm_neg] at this
        simp only [Complex.norm_natCast] at this
        exact_mod_cast this
      have hT : T = 2 * D := by omega
      rcases hT2.1 hT with ⟨rfl, hk⟩ | ⟨rfl, rfl⟩
      · right; right; refine ⟨rfl, hk, ?_⟩
        have hp : (2 : ℤ) ^ v = 2 ^ (v - 1) * 2 := by rw [← pow_succ]; congr 1; omega
        push_cast at h0 h1
        obtain ⟨k, hk'⟩ := (Int.modEq_iff_dvd.1 h0)
        rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · exact absurd (Int.modEq_iff_dvd.2 ⟨j, by rw [hp]; linear_combination hk'⟩) h1
        · rw [Int.modEq_iff_dvd]; exact ⟨j + 1, by rw [hp]; linear_combination hk'⟩
      · right; left; refine ⟨rfl, rfl, ?_⟩
        have hu : (z : ZMod 3) ≠ 0 := by
          rw [show ((z : ℤ) : ZMod 3) = (g : ZMod (3 ^ 1)) from hz]; exact g.ne_zero
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at hu
        simp only [Int.ModEq, pow_one, Nat.cast_ofNat] at h1 ⊢
        push_cast at hu
        omega
    · rw [if_neg (fun h => h0 (e0.1 h)), neg_zero] at hS
      have : (Pr.card : ℂ) ≠ 0 := by exact_mod_cast (show Pr.card ≠ 0 by omega)
      rcases mul_eq_zero.1 hS with h | h
      · exact absurd h this
      · rw [h, norm_zero] at hcn; exact absurd hcn zero_ne_one
  · intro hsp; exact ⟨_, hval hsp⟩
end PP
end Erdos634.LemmaSGpp
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSPhi
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.DirichletCRT (conductor_eq primitiveCharacter_eq)
theorem changeLevel_nat {d n : ℕ} (hd : d ∣ n) (ω : DirichletCharacter ℂ d) (b : ℕ)
    (hb : b.Coprime n) : changeLevel hd ω (b : ZMod n) = ω (b : ZMod d) := by
  have := changeLevel_eq_cast_of_dvd ω hd (ZMod.unitOfCoprime b hb)
  rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] at this
  exact this
theorem primChar_nat_of_isPrimitive {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ.IsPrimitive) (b : ℕ) : ψ.primitiveCharacter (b : ZMod ψ.conductor) = ψ (b : ZMod N) := by
  have hc : ψ.conductor = N := hψ
  by_cases hb : b.Coprime N
  · conv_rhs => rw [← changeLevel_primitiveCharacter ψ]
    rw [changeLevel_nat _ _ b hb]
  · have h1 : ¬ IsUnit (b : ZMod ψ.conductor) := by rw [ZMod.isUnit_iff_coprime, hc]; exact hb
    have h2 : ¬ IsUnit (b : ZMod N) := by rw [ZMod.isUnit_iff_coprime]; exact hb
    rw [MulChar.map_nonunit _ h1, MulChar.map_nonunit _ h2]
theorem primChar_mul_nat {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] (h : m₁.Coprime m₂)
    {χ : DirichletCharacter ℂ (m₁ * m₂)} {ψ : DirichletCharacter ℂ m₁} {η : DirichletCharacter ℂ m₂}
    (hχ : χ = changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η)
    (b : ℕ) :
    χ.primitiveCharacter (b : ZMod χ.conductor) =
      ψ.primitiveCharacter (b : ZMod ψ.conductor) * η.primitiveCharacter (b : ZMod η.conductor) := by
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hc := conductor_eq h hχ
  rw [primitiveCharacter_eq h hχ, MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases hb : b.Coprime χ.conductor
  · have hb' := hb; rw [hc] at hb'
    rw [changeLevel_nat _ _ b hb, changeLevel_nat _ _ b hb]
  · have h1 : ¬ IsUnit (b : ZMod χ.conductor) := by rw [ZMod.isUnit_iff_coprime]; exact hb
    rw [MulChar.map_nonunit _ h1, MulChar.map_nonunit _ h1, zero_mul]
    rw [hc, Nat.coprime_mul_iff_right, not_and_or] at hb
    rcases hb with hb | hb
    · rw [MulChar.map_nonunit ψ.primitiveCharacter (by rw [ZMod.isUnit_iff_coprime]; exact hb),
        zero_mul]
    · rw [MulChar.map_nonunit η.primitiveCharacter (by rw [ZMod.isUnit_iff_coprime]; exact hb),
        mul_zero]
section Comp
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m] (hr : 1 ≤ r) (hpm : ¬ p ∣ m)
  {ψ : DirichletCharacter ℂ (p ^ r)} (hψ : ψ.IsPrimitive) (η : DirichletCharacter ℂ m)
instance neZero_pr : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
instance neZero_prm : NeZero (p ^ r * m) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
theorem cop_pr (hpm : ¬ p ∣ m) : (p ^ r).Coprime m :=
  Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm)
noncomputable abbrev chi (ψ : DirichletCharacter ℂ (p ^ r)) (η : DirichletCharacter ℂ m) :
    DirichletCharacter ℂ (p ^ r * m) :=
  changeLevel (Nat.dvd_mul_right (p ^ r) m) ψ * changeLevel (Nat.dvd_mul_left m (p ^ r)) η
include hpm hψ in
theorem conductor_chi : (chi ψ η).conductor = p ^ r * η.conductor := by
  rw [conductor_eq (cop_pr hpm) rfl, show ψ.conductor = p ^ r from hψ]
def dm (m a : ℕ) : ℕ := m / m.gcd a
include hr hpm hψ in
theorem bracket_p_dvd (a : ℕ) (ha : p ∣ a) : bracket (chi ψ η) a = 0 := by
  unfold bracket
  rw [if_neg]
  rw [conductor_chi hpm hψ η]
  intro hdv
  set n := p ^ r * m
  have hg : n.gcd a ∣ n := Nat.gcd_dvd_left n a
  have h1 : p ^ r ∣ n / n.gcd a := dvd_trans (Nat.dvd_mul_right _ _) hdv
  have h2 : p ^ r * n.gcd a ∣ n := by
    have := Nat.mul_dvd_mul_right h1 (n.gcd a)
    rwa [Nat.div_mul_cancel hg] at this
  have h3 : n.gcd a ∣ m := (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos r) h2)
  have h4 : p ∣ n.gcd a := Nat.dvd_gcd (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m) ha
  exact hpm (dvd_trans h4 h3)
include hpm in
theorem gcd_eq (a : ℕ) (ha : ¬ p ∣ a) : (p ^ r * m).gcd a = m.gcd a :=
  Nat.Coprime.gcd_mul_left_cancel m (Nat.Coprime.pow_left r
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 ha))
include hpm in
theorem euler_eq (d f : ℕ) (hd : d ∣ m) (hd0 : d ≠ 0) (hf0 : f ≠ 0) :
    eulerPrimes (p ^ r * d) (p ^ r * f) = eulerPrimes d f := by
  ext ℓ
  simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors]
  have hP0 : p ^ r ≠ 0 := NeZero.ne _
  constructor
  · rintro ⟨⟨hl, hdv, -⟩, hn⟩
    have hlp : ¬ ℓ ∣ p ^ r := fun h' => hn (dvd_mul_of_dvd_left h' _)
    refine ⟨⟨hl, (hl.dvd_mul.1 hdv).resolve_left hlp, hd0⟩, fun h' => hn (dvd_mul_of_dvd_right h' _)⟩
  · rintro ⟨⟨hl, hdv, -⟩, hn⟩
    refine ⟨⟨hl, dvd_mul_of_dvd_right hdv _, Nat.mul_ne_zero hP0 hd0⟩, fun h' => ?_⟩
    rcases hl.dvd_mul.1 h' with h' | h'
    · have := (Nat.prime_dvd_prime_iff_eq hl hp.out).1 (hl.dvd_of_dvd_pow h')
      subst this; exact hpm (dvd_trans hdv hd)
    · exact hn h'
include hpm hψ in
theorem bracket_unit (a : ℕ) (ha : ¬ p ∣ a) :
    bracket (chi ψ η) a =
      if η.conductor ∣ dm m a then
        ((m.totient : ℂ) / (dm m a).totient) * ψ ((a / m.gcd a : ℕ) : ZMod (p ^ r))
          * η.primitiveCharacter ((a / m.gcd a : ℕ) : ZMod η.conductor)
          * ∏ ℓ ∈ eulerPrimes (dm m a) η.conductor,
              (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
      else 0 := by
  have hcop := cop_pr (r := r) hpm
  have hg := gcd_eq (r := r) hpm a ha
  have hdm : dm m a ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m a)
  have hd0 : dm m a ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left m a)
    rw [show m / m.gcd a = 0 from h0, zero_mul] at this
    exact NeZero.ne m this.symm
  have hnd : p ^ r * m / m.gcd a = p ^ r * dm m a := Nat.mul_div_assoc _ (Nat.gcd_dvd_left m a)
  have hP : 0 < p ^ r := pow_pos hp.out.pos r
  unfold bracket
  rw [hg, hnd]
  by_cases hf : η.conductor ∣ dm m a
  · rw [if_pos (by rw [conductor_chi hpm hψ η]; exact Nat.mul_dvd_mul_left _ hf), if_pos hf]
    have hE : eulerPrimes (p ^ r * dm m a) (chi ψ η).conductor = eulerPrimes (dm m a) η.conductor := by
      rw [conductor_chi hpm hψ η]; exact euler_eq hpm _ _ hdm hd0 (conductor_ne_zero η)
    have hT : (((p ^ r * m).totient : ℕ) : ℂ) / ((p ^ r * dm m a).totient : ℕ)
        = (m.totient : ℂ) / (dm m a).totient := by
      rw [Nat.totient_mul hcop, Nat.totient_mul (hcop.coprime_dvd_right hdm)]
      push_cast
      exact mul_div_mul_left _ _ (by exact_mod_cast (Nat.totient_pos.2 hP).ne')
    rw [hE, hT, primChar_mul_nat (cop_pr hpm) rfl, primChar_nat_of_isPrimitive hψ]
    have hprod : ∀ ℓ ∈ eulerPrimes (dm m a) η.conductor,
        (1 - (chi ψ η).primitiveCharacter⁻¹ (ℓ : ZMod (chi ψ η).conductor))
          = (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor)) := by
      intro ℓ _
      simp only [MulChar.inv_apply_eq_inv']
      rw [primChar_mul_nat (cop_pr hpm) rfl, primChar_nat_of_isPrimitive hψ, mul_inv]
    rw [prod_congr rfl hprod]
    ring
  · rw [if_neg hf, if_neg]
    intro h
    rw [conductor_chi hpm hψ η] at h
    exact hf (Nat.dvd_of_mul_dvd_mul_left hP h)
theorem sum_indicator {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (L x : ZMod N) (hL : IsUnit L) :
    ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * (if (u : ZMod N) * L = x then 1 else 0) = ψ x * (ψ L)⁻¹ := by
  by_cases hx : IsUnit x
  · obtain ⟨Lu, rfl⟩ := hL
    obtain ⟨xu, rfl⟩ := hx
    set u0 : (ZMod N)ˣ := xu * Lu⁻¹
    have hu0 : ((u0 : (ZMod N)ˣ) : ZMod N) * (Lu : ZMod N) = xu := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [sum_eq_single u0]
    · rw [if_pos hu0, mul_one]
      have hψL : ψ (Lu : ZMod N) ≠ 0 := Erdos634.DirichletCRT.unit_val_ne_zero ψ _
      rw [eq_mul_inv_iff_mul_eq₀ hψL, ← map_mul, hu0]
    · intro u _ hne
      rw [if_neg, mul_zero]
      intro h
      apply hne
      have : (((u * Lu : (ZMod N)ˣ)) : ZMod N) = ((u0 * Lu : (ZMod N)ˣ) : ZMod N) := by
        rw [Units.val_mul, Units.val_mul, h, hu0]
      exact mul_right_cancel (Units.ext this)
    · intro h; exact absurd (mem_univ _) h
  · rw [MulChar.map_nonunit ψ hx, zero_mul]
    refine sum_eq_zero (fun u _ => ?_)
    rw [if_neg, mul_zero]
    intro h; exact hx (h ▸ u.isUnit.mul hL)
end Comp
end Erdos634.LemmaSPhi
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSGprime
open Erdos634.LemmaSGpp (SpPP lemmaGpp exists_primitive_pp)
open Erdos634.DirichletCRT (unitsCRT unitsCRT_fst unitsCRT_snd const_iff decomp prod_unit isPrimitive_iff)
def Sp (d : ℕ) (z : ℤ) : Prop := ∀ q ∈ d.primeFactors, SpPP q (d.factorization q) z
noncomputable def tau (d : ℕ) (z : ℤ) : ℕ := by
  classical
  exact (d.primeFactors.filter (fun q : ℕ => ¬ z ≡ 1 [ZMOD (q : ℤ) ^ d.factorization q])).card
theorem Sp_pp {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (z : ℤ) : Sp (p ^ n) z ↔ SpPP p n z := by
  simp [Sp, Nat.primeFactors_prime_pow hn hp, hp.factorization_self]
theorem tau_pp {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (z : ℤ) :
    tau (p ^ n) z = if z ≡ 1 [ZMOD (p : ℤ) ^ n] then 0 else 1 := by
  classical
  unfold tau
  rw [Nat.primeFactors_prime_pow hn hp, filter_singleton, Nat.factorization_pow_self hp]
  split_ifs <;> simp_all
section Mul
variable {a b : ℕ} (h : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0)
include h ha hb
omit ha hb in
theorem fact_left {q : ℕ} (hq : q ∈ a.primeFactors) : (a * b).factorization q = a.factorization q :=
  Nat.factorization_eq_of_coprime_left h (Nat.mem_primeFactors_iff_mem_primeFactorsList.1 hq)
omit ha hb in
theorem fact_right {q : ℕ} (hq : q ∈ b.primeFactors) : (a * b).factorization q = b.factorization q :=
  Nat.factorization_eq_of_coprime_right h (Nat.mem_primeFactors_iff_mem_primeFactorsList.1 hq)
theorem Sp_mul (z : ℤ) : Sp (a * b) z ↔ Sp a z ∧ Sp b z := by
  unfold Sp
  rw [Nat.primeFactors_mul ha hb]
  constructor
  · intro H
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · have := H q (mem_union_left _ hq); rwa [fact_left h hq] at this
    · have := H q (mem_union_right _ hq); rwa [fact_right h hq] at this
  · rintro ⟨Ha, Hb⟩ q hq
    rcases mem_union.1 hq with hq | hq
    · rw [fact_left h hq]; exact Ha q hq
    · rw [fact_right h hq]; exact Hb q hq
theorem tau_mul (z : ℤ) : tau (a * b) z = tau a z + tau b z := by
  classical
  unfold tau
  rw [Nat.primeFactors_mul ha hb, filter_union, card_union_of_disjoint
    (disjoint_filter_filter h.disjoint_primeFactors)]
  congr 1
  · congr 1; apply filter_congr; intro q hq; rw [fact_left h hq]
  · congr 1; apply filter_congr; intro q hq; rw [fact_right h hq]
end Mul
def Stmt (d : ℕ) : Prop :=
  d ≠ 0 → d % 4 ≠ 2 → (∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive) ∧
    ∀ (g : (ZMod d)ˣ) (z : ℤ), ((z : ℤ) : ZMod d) = g →
      ((∃ c : ℂ, ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ (g : ZMod d) = c) ↔ Sp d z) ∧
      (Sp d z → ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ (g : ZMod d) = (-1) ^ tau d z)
theorem mod4_left {a b : ℕ} (h : a.Coprime b) (hab : (a * b) % 4 ≠ 2) : a % 4 ≠ 2 := by
  intro ha
  have h2a : 2 ∣ a := by omega
  have hb : ¬ 2 ∣ b := fun h2b => by
    have := Nat.dvd_gcd h2a h2b; rw [h.gcd_eq_one] at this; omega
  apply hab
  rw [Nat.mul_mod, ha]
  have : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases this with e | e <;> rw [e]
theorem stmt_all (d : ℕ) : Stmt d := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ _
    refine ⟨⟨1, DirichletCharacter.isPrimitive_one_level_one⟩, fun g z _ => ?_⟩
    have hg : (g : ZMod 1) = 1 := Subsingleton.elim _ _
    have hS : Sp 1 z := by simp [Sp]
    have ht : tau 1 z = 0 := by simp [tau]
    refine ⟨⟨fun _ => hS, fun _ => ⟨1, fun χ _ => by rw [hg, map_one]⟩⟩, fun _ χ _ => ?_⟩
    rw [hg, map_one, ht, pow_zero]
  | prime_pow p n hp hn =>
    intro _ h4
    haveI : Fact p.Prime := ⟨hp⟩
    have h2 : p ^ n ≠ 2 := fun e => h4 (by rw [e])
    refine ⟨exists_primitive_pp hn h2, fun g z hz => ?_⟩
    obtain ⟨H1, H2⟩ := lemmaGpp hn h2 g z hz
    rw [Sp_pp hp hn.ne' z, tau_pp hp hn.ne' z]
    refine ⟨H1, fun hs χ hχ => ?_⟩
    rw [H2 hs χ hχ]
    split_ifs <;> simp
  | coprime a b ha hb h IHa IHb =>
    intro _ h4
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    haveI : NeZero a := ⟨ha0⟩
    haveI : NeZero b := ⟨hb0⟩
    have h4a := mod4_left h h4
    have h4b : b % 4 ≠ 2 := mod4_left h.symm (by rwa [mul_comm])
    obtain ⟨⟨ψ, hψ⟩, Ga⟩ := IHa ha0 h4a
    obtain ⟨⟨η, hη⟩, Gb⟩ := IHb hb0 h4b
    refine ⟨⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩⟩, fun g z hz => ?_⟩
    have hz₁ : ((z : ℤ) : ZMod a) = ((unitsCRT h g).1 : ZMod a) := by
      rw [unitsCRT_fst, ZMod.unitsMap_val, ← hz, ZMod.cast_intCast (Nat.dvd_mul_right a b)]
    have hz₂ : ((z : ℤ) : ZMod b) = ((unitsCRT h g).2 : ZMod b) := by
      rw [unitsCRT_snd, ZMod.unitsMap_val, ← hz, ZMod.cast_intCast (Nat.dvd_mul_left b a)]
    obtain ⟨A1, A2⟩ := Ga _ z hz₁
    obtain ⟨B1, B2⟩ := Gb _ z hz₂
    refine ⟨?_, fun hs χ hχ => ?_⟩
    · rw [const_iff h g ⟨ψ, hψ⟩ ⟨η, hη⟩, A1, B1, Sp_mul h ha0 hb0]
    · obtain ⟨sa, sb⟩ := (Sp_mul h ha0 hb0 z).1 hs
      have e := decomp h χ
      obtain ⟨p1, p2⟩ := (isPrimitive_iff h e).1 hχ
      rw [e, prod_unit h, A2 sa _ p1, B2 sb _ p2, ← pow_add, tau_mul h ha0 hb0]
theorem exists_primitive {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 ≠ 2) :
    ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive := (stmt_all d hd0 hd).1
theorem lemmaG' {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 ≠ 2) (g : (ZMod d)ˣ) (z : ℤ)
    (hz : ((z : ℤ) : ZMod d) = g) :
    ((∃ c : ℂ, ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ (g : ZMod d) = c) ↔ Sp d z) ∧
    (Sp d z → ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ (g : ZMod d) = (-1) ^ tau d z) :=
  (stmt_all d hd0 hd).2 g z hz
end Erdos634.LemmaSGprime
end

section
open scoped BigOperators
open DirichletCharacter
namespace Erdos634.LemmaSG
variable {n : ℕ} [NeZero n]
theorem val_neg_one (χ : DirichletCharacter ℂ n) : χ (-1) = 1 ∨ χ (-1) = -1 :=
  χ.even_or_odd
theorem parity_sum (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (g : ZMod n) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = ε), 2 * χ g =
      (∑ χ : DirichletCharacter ℂ n, χ g) + ε * ∑ χ : DirichletCharacter ℂ n, χ (-g) := by
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have hm : χ (-g) = χ (-1) * χ g := by rw [← map_mul]; ring_nf
  rw [hm]
  rcases val_neg_one χ with h | h <;> rcases hε with rfl | rfl <;> simp [h]
  all_goals first | (intro hh; norm_num at hh) | ring
theorem S_zero {g : ZMod n} (hg : g ≠ 1) : ∑ χ : DirichletCharacter ℂ n, χ g = 0 :=
  sum_characters_eq_zero ℂ hg
theorem lemmaG_odd_general (h3 : (-1 : ZMod n) ≠ 1) {g : ZMod n} (hg : IsUnit g) (c : ℂ)
    (hc : ∀ χ : DirichletCharacter ℂ n, χ.Odd → χ g = c) : g = 1 ∨ g = -1 := by
  by_contra hne
  push_neg at hne
  have h1 : -g ≠ 1 := fun h => hne.2 (by rw [← neg_neg g, h])
  have hs := parity_sum (-1) (Or.inr rfl) g
  rw [S_zero hne.1, S_zero h1, mul_zero, add_zero] at hs
  obtain ⟨χ₀, hχ₀⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ h3
  have ho : χ₀ (-1) = -1 := (val_neg_one χ₀).resolve_left hχ₀
  have hc0 : c ≠ 0 := by
    rw [← hc χ₀ ho]
    intro h0
    have := χ₀.unit_norm_eq_one hg.unit
    rw [IsUnit.unit_spec, h0, norm_zero] at this
    exact zero_ne_one this
  rw [Finset.sum_congr rfl (fun χ hχ => by rw [hc χ (Finset.mem_filter.mp hχ).2]),
    Finset.sum_const, nsmul_eq_mul] at hs
  have hmem : χ₀ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = -1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩
  have hcard : ((Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = -1)).card : ℂ) ≠ 0 :=
    by exact_mod_cast (Finset.card_pos.mpr ⟨χ₀, hmem⟩).ne'
  exact mul_ne_zero hcard (mul_ne_zero two_ne_zero hc0) hs
theorem lemmaG_even_general (h3 : (-1 : ZMod n) ≠ 1) (hφ : 6 ≤ n.totient) {g : ZMod n}
    (hg : IsUnit g) (c : ℂ) (hc : ∀ χ : DirichletCharacter ℂ n, χ.Even → χ ≠ 1 → χ g = c) :
    g = 1 ∨ g = -1 := by
  by_contra hne
  push_neg at hne
  have h1 : -g ≠ 1 := fun h => hne.2 (by rw [← neg_neg g, h])
  set E := Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = 1) with hE
  have hcount := parity_sum 1 (Or.inl rfl) (1 : ZMod n)
  rw [← hE, sum_characters_eq, S_zero (by rwa [ne_eq] : -(1 : ZMod n) ≠ 1)] at hcount
  simp only [map_one, mul_one, if_true, Finset.sum_const, nsmul_eq_mul] at hcount
  have hs := parity_sum 1 (Or.inl rfl) g
  rw [← hE, S_zero hne.1, S_zero h1, mul_zero, add_zero, ← Finset.mul_sum] at hs
  have hs' : ∑ χ ∈ E, χ g = 0 := by
    rcases mul_eq_zero.mp hs with h | h
    · norm_num at h
    · exact h
  have h1E : (1 : DirichletCharacter ℂ n) ∈ E :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, MulChar.one_apply isUnit_one.neg⟩
  rw [← Finset.add_sum_erase _ _ h1E, MulChar.one_apply hg,
    Finset.sum_congr rfl (fun χ hχ => by
      rw [hc χ (Finset.mem_filter.mp (Finset.mem_of_mem_erase hχ)).2
        (Finset.ne_of_mem_erase hχ)]),
    Finset.sum_const, nsmul_eq_mul] at hs'
  have hEcard : 3 ≤ E.card := by
    have : ((2 * E.card : ℕ) : ℂ) = (n.totient : ℂ) := by push_cast; linear_combination hcount
    have := Nat.cast_injective this
    omega
  have hEr : 2 ≤ (E.erase 1).card := by rw [Finset.card_erase_of_mem h1E]; omega
  obtain ⟨χ₁, hχ₁⟩ := Finset.card_pos.mp (by omega : 0 < (E.erase 1).card)
  have hnc : ‖c‖ = 1 := by
    rw [← hc χ₁ (Finset.mem_filter.mp (Finset.mem_of_mem_erase hχ₁)).2 (Finset.ne_of_mem_erase hχ₁)]
    have := χ₁.unit_norm_eq_one hg.unit
    rwa [IsUnit.unit_spec] at this
  have heq : ((E.erase 1).card : ℂ) * c = -1 := by linear_combination hs'
  have hn := congrArg norm heq
  rw [norm_mul, hnc, mul_one, norm_neg, norm_one, Complex.norm_natCast] at hn
  have : ((E.erase 1).card : ℝ) ≥ 2 := by exact_mod_cast hEr
  linarith
end Erdos634.LemmaSG
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSG2
open Erdos634.LemmaSN (pred_dvd isPrimitive_iff_not_factorsThrough)
theorem changeLevel_neg_one {m n : ℕ} [NeZero n] (h : m ∣ n) (ψ : DirichletCharacter ℂ m) :
    DirichletCharacter.changeLevel h ψ (-1) = ψ (-1) := by
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ h (-1)
  simp only [Units.val_neg, Units.val_one] at h1
  rw [h1, ZMod.cast_neg h, ZMod.cast_one h]
theorem lemmaG_pow {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 2 ≤ r) {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1) (g : (ZMod (p ^ r))ˣ) (c : ℂ)
    (hc : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ψ (g : ZMod (p ^ r)) = c) :
    (g : ZMod (p ^ r)) = 1 ∨ (g : ZMod (p ^ r)) = -1 := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (p ^ (r - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hq'7 : 7 ≤ p ^ (r - 1) := le_trans hp7 (Nat.le_self_pow (by omega) p)
  have hq7 : 7 ≤ p ^ r := le_trans hp7 (Nat.le_self_pow (by omega) p)
  haveI : Fact (2 < p ^ (r - 1)) := ⟨by omega⟩
  haveI : Fact (2 < p ^ r) := ⟨by omega⟩
  have hm1 : (-1 : ZMod (p ^ r)) ≠ 1 := ZMod.neg_one_ne_one
  have hm1' : (-1 : ZMod (p ^ (r - 1))) ≠ 1 := ZMod.neg_one_ne_one
  have hd := pred_dvd p r
  have htot : (p ^ r).totient = p * (p ^ (r - 1)).totient := by
    rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]
    exact Nat.totient_mul_of_prime_of_dvd hp.out (dvd_pow_self p (by omega))
  have hT0 : 0 < (p ^ (r - 1)).totient := Nat.totient_pos.2 (by positivity)
  by_contra hne
  push Not at hne
  set X := univ.filter (fun ψ : DirichletCharacter ℂ (p ^ r) => ψ (-1) = ε) with hX
  set X' := univ.filter (fun ψ : DirichletCharacter ℂ (p ^ (r - 1)) => ψ (-1) = ε) with hX'
  set Xp := X.filter (fun ψ => ψ.IsPrimitive) with hXp
  have hsplit : ∀ F : DirichletCharacter ℂ (p ^ r) → ℂ,
      ∑ ψ ∈ X, F ψ = ∑ ψ ∈ Xp, F ψ + ∑ ψ' ∈ X', F (DirichletCharacter.changeLevel hd ψ') := by
    intro F
    rw [← sum_filter_add_sum_filter_not X (fun ψ => ψ.IsPrimitive) F]
    congr 1
    have hY : X.filter (fun ψ => ¬ ψ.IsPrimitive)
        = X'.map ⟨DirichletCharacter.changeLevel hd, DirichletCharacter.changeLevel_injective hd⟩ := by
      ext ψ
      simp only [hX, hX', mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hpar, hnp⟩
        have hf : ψ.FactorsThrough (p ^ (r - 1)) :=
          not_not.1 (fun h' => hnp ((isPrimitive_iff_not_factorsThrough (by omega) ψ).2 h'))
        have heq := hf.eq_changeLevel
        refine ⟨hf.χ₀, ?_, heq.symm⟩
        rw [← changeLevel_neg_one hd, ← heq]; exact hpar
      · rintro ⟨ψ', hpar, rfl⟩
        refine ⟨by rw [changeLevel_neg_one]; exact hpar, fun hprim => ?_⟩
        exact (isPrimitive_iff_not_factorsThrough (by omega) _).1 hprim ⟨hd, ψ', rfl⟩
    rw [hY, sum_map]
    rfl
  have hval : ∀ (ψ' : DirichletCharacter ℂ (p ^ (r - 1))) (u : (ZMod (p ^ r))ˣ),
      DirichletCharacter.changeLevel hd ψ' (u : ZMod (p ^ r))
        = ψ' ((ZMod.unitsMap hd u : (ZMod (p ^ (r - 1)))ˣ) : ZMod (p ^ (r - 1))) := by
    intro ψ' u
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]
  have hXpval : ∀ u : (ZMod (p ^ r))ˣ, (∀ ψ ∈ Xp, ψ (u : ZMod (p ^ r)) = c) →
      ∑ ψ ∈ Xp, 2 * ψ (u : ZMod (p ^ r)) = 2 * (Xp.card : ℂ) * c := by
    intro u hu
    rw [sum_congr rfl (fun ψ hψ => by rw [hu ψ hψ]), sum_const, nsmul_eq_mul]; ring
  have hcXp : ∀ ψ ∈ Xp, ψ (g : ZMod (p ^ r)) = c := by
    intro ψ hψ
    obtain ⟨h1, h2⟩ := mem_filter.1 hψ
    exact hc ψ h2 (mem_filter.1 h1).2
  have hP1 := Erdos634.LemmaSG.parity_sum ε hε (1 : ZMod (p ^ r))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl,
    if_neg hm1, mul_zero, add_zero] at hP1
  rw [← hX, hsplit (fun ψ => 2 * ψ 1)] at hP1
  simp only [MulChar.map_one, mul_one, sum_const, nsmul_eq_mul] at hP1
  have hP1' := Erdos634.LemmaSG.parity_sum ε hε (1 : ZMod (p ^ (r - 1)))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl,
    if_neg hm1', mul_zero, add_zero] at hP1'
  rw [← hX'] at hP1'
  simp only [MulChar.map_one, mul_one, sum_const, nsmul_eq_mul] at hP1'
  have hcount : 2 * Xp.card + (p ^ (r - 1)).totient = (p ^ r).totient := by
    have : ((2 * Xp.card + (p ^ (r - 1)).totient : ℕ) : ℂ) = ((p ^ r).totient : ℂ) := by
      push_cast; rw [← hP1, ← hP1']; ring
    exact_mod_cast this
  have hPg := Erdos634.LemmaSG.parity_sum ε hε (g : ZMod (p ^ r))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_neg hne.1,
    if_neg (fun h => hne.2 (by rw [← neg_neg (g : ZMod (p ^ r)), h])), mul_zero, add_zero] at hPg
  rw [← hX, hsplit (fun ψ => 2 * ψ (g : ZMod (p ^ r))), hXpval g hcXp] at hPg
  simp only [hval] at hPg
  set gb : ZMod (p ^ (r - 1)) := ((ZMod.unitsMap hd g : (ZMod (p ^ (r - 1)))ˣ) : ZMod (p ^ (r - 1)))
  have hPg' := Erdos634.LemmaSG.parity_sum ε hε gb
  rw [← hX'] at hPg'
  rw [hPg', DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ] at hPg
  have hXpos : 0 < Xp.card := by
    have : 0 < 2 * Xp.card := by
      have h2 := htot; nlinarith [hcount, hT0, hp7]
    omega
  obtain ⟨ψ0, hψ0⟩ := card_pos.1 hXpos
  have hcn : ‖c‖ = 1 := by rw [← hcXp ψ0 hψ0]; exact ψ0.unit_norm_eq_one g
  have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hind : ∀ x : ZMod (p ^ (r - 1)),
      ‖(if x = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0)‖ ≤ (p ^ (r - 1)).totient := by
    intro x; split_ifs <;> simp
  have hnorm : ((2 * Xp.card : ℕ) : ℝ) ≤ 2 * (p ^ (r - 1)).totient := by
    have heq : 2 * (Xp.card : ℂ) * c = -((if gb = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0)
        + ε * (if -gb = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0)) := by
      linear_combination hPg
    have := congrArg norm heq
    rw [norm_neg, norm_mul, norm_mul, hcn, mul_one] at this
    have hle := norm_add_le (if gb = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0)
      (ε * (if -gb = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0))
    rw [norm_mul, hεn, one_mul] at hle
    have h1 := hind gb
    have h2 := hind (-gb)
    push_cast
    have : ‖(2 : ℂ)‖ * ‖(Xp.card : ℂ)‖ = 2 * (Xp.card : ℝ) := by simp
    linarith
  have hnat : 2 * Xp.card ≤ 2 * (p ^ (r - 1)).totient := by exact_mod_cast hnorm
  have : p * (p ^ (r - 1)).totient ≤ 3 * (p ^ (r - 1)).totient := by rw [← htot]; omega
  have := Nat.le_of_mul_le_mul_right this hT0
  omega
theorem isPrimitive_of_ne_one {p : ℕ} [hp : Fact p.Prime] {ψ : DirichletCharacter ℂ (p ^ 1)}
    (h : ψ ≠ 1) : ψ.IsPrimitive := by
  refine (isPrimitive_iff_not_factorsThrough le_rfl ψ).2 (fun hf => h ?_)
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact (DirichletCharacter.factorsThrough_one_iff ψ).1 hf
theorem lemmaG {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1) (g : (ZMod (p ^ r))ˣ) (c : ℂ)
    (hc : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ψ (g : ZMod (p ^ r)) = c) :
    (g : ZMod (p ^ r)) = 1 ∨ (g : ZMod (p ^ r)) = -1 := by
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    haveI : Fact (2 < p ^ 1) := ⟨by rw [pow_one]; omega⟩
    have hm1 : (-1 : ZMod (p ^ 1)) ≠ 1 := ZMod.neg_one_ne_one
    rcases hε with rfl | rfl
    · refine Erdos634.LemmaSG.lemmaG_even_general hm1 ?_ g.isUnit c
        (fun χ he hne => hc χ (isPrimitive_of_ne_one hne) he)
      rw [pow_one, Nat.totient_prime hp.out]; omega
    · exact Erdos634.LemmaSG.lemmaG_odd_general hm1 g.isUnit c
        (fun χ ho => hc χ (isPrimitive_of_ne_one (Erdos634.LemmaSB1.ne_one_of_odd ho)) ho)
  · exact lemmaG_pow hp7 h hε g c hc
end Erdos634.LemmaSG2
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSIso
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit cop_pr)
def fpc (d : ℕ) : ℕ := if d % 4 = 2 then d / 2 else d
theorem fpc_dvd (d : ℕ) : fpc d ∣ d := by
  unfold fpc; split_ifs with h
  · exact Nat.div_dvd_of_dvd (by omega)
  · exact dvd_rfl
theorem fpc_mod4 (d : ℕ) : fpc d % 4 ≠ 2 := by unfold fpc; split_ifs <;> omega
theorem fpc_ne_zero {d : ℕ} (hd : d ≠ 0) : fpc d ≠ 0 := by unfold fpc; split_ifs <;> omega
theorem euler_fpc {d ℓ : ℕ} (hl : ℓ ∈ eulerPrimes d (fpc d)) : ℓ = 2 := by
  simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors] at hl
  obtain ⟨⟨hl, hld, -⟩, hn⟩ := hl
  unfold fpc at hn
  split_ifs at hn with h
  · have h2 : d = 2 * (d / 2) := by omega
    rw [h2] at hld
    rcases hl.dvd_mul.1 hld with h' | h'
    · exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h'
    · exact absurd h' hn
  · exact absurd hld hn
theorem conductor_changeLevel_of_isPrimitive {f m : ℕ} [NeZero m] [NeZero f] (h : f ∣ m)
    {η₀ : DirichletCharacter ℂ f} (hη₀ : η₀.IsPrimitive) : (changeLevel h η₀).conductor = f := by
  set η := changeLevel h η₀
  have hcf : η.conductor ∣ f := conductor_dvd_of_mem_conductorSet η ⟨h, η₀, rfl⟩
  refine Nat.dvd_antisymm hcf ?_
  have hft : η₀.FactorsThrough η.conductor := by
    rw [factorsThrough_iff_ker_unitsMap hcf]
    intro u hu
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective h u
    have hv : v ∈ (ZMod.unitsMap (dvd_trans hcf h)).ker := by
      rw [MonoidHom.mem_ker, ← ZMod.unitsMap_comp hcf h, MonoidHom.comp_apply]
      exact hu
    have := (factorsThrough_iff_ker_unitsMap (dvd_trans hcf h)).1 (factorsThrough_conductor η) hv
    rw [MonoidHom.mem_ker] at this ⊢
    rwa [changeLevel_toUnitHom, MonoidHom.comp_apply] at this
  have := conductor_dvd_of_mem_conductorSet η₀ hft
  rwa [show η₀.conductor = f from hη₀] at this
theorem primChar_ne_zero {N : ℕ} [NeZero N] (η : DirichletCharacter ℂ N) (b : ℕ)
    (hb : b.Coprime η.conductor) : η.primitiveCharacter (b : ZMod η.conductor) ≠ 0 := by
  haveI : NeZero η.conductor := ⟨conductor_ne_zero η⟩
  rw [← ZMod.coe_unitOfCoprime b hb]
  exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
theorem two_ne_pm_one {P : ℕ} (hP : 7 ≤ P) :
    ((2 : ℕ) : ZMod P) ≠ 1 ∧ ((2 : ℕ) : ZMod P) ≠ -1 := by
  constructor
  · intro h
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega
  · intro h
    have h3 : ((3 : ℕ) : ZMod P) = 0 := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, Nat.cast_add, h, Nat.cast_one]; ring
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
section Iso
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem lemmaIso (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (j : ι) (hj : ¬ p ∣ a j)
    (hiso : ∀ k, k ≠ j → ¬ p ∣ a k → e k ≠ 0 → ¬ fpc (dm m (a j)) ∣ dm m (a k)) :
    e j = 0 := by
  by_contra hej
  have hP7 : 7 ≤ p ^ r := le_trans hp7 (Nat.le_self_pow (by omega) p)
  set d := dm m (a j) with hd
  set f := fpc d with hf
  have hdm : d ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m (a j))
  have hd0 : d ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left m (a j))
    rw [show m / m.gcd (a j) = 0 from h0, zero_mul] at this
    exact NeZero.ne m this.symm
  have hfd : f ∣ d := fpc_dvd d
  have hfm : f ∣ m := dvd_trans hfd hdm
  haveI : NeZero f := ⟨fpc_ne_zero hd0⟩
  obtain ⟨η₀, hη₀⟩ := Erdos634.LemmaSGprime.exists_primitive (fpc_ne_zero hd0) (fpc_mod4 d)
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  set ε : ℂ := -η (-1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases η.even_or_odd with h | h
    · right; simp only [ε, show η (-1) = 1 from h]
    · left; simp only [ε, show η (-1) = -1 from h, neg_neg]
  set b := a j / m.gcd (a j)
  have hgpos : 0 < m.gcd (a j) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have hbd : d.Coprime b := Nat.coprime_div_gcd_div_gcd hgpos
  have hbf : b.Coprime η.conductor := by rw [hηc]; exact (hbd.coprime_dvd_left hfd).symm
  have hbP : b.Coprime (p ^ r) := by
    refine Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 ?_).symm
    exact fun h => hj (dvd_trans h (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m (a j))))
  have key : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∏ ℓ ∈ eulerPrimes d η.conductor,
        (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor)) = 0 := by
    intro ψ hψ hψε
    have hη2 : η (-1) * η (-1) = 1 := by
      rcases η.even_or_odd with h | h
      · rw [show η (-1) = 1 from h]; ring
      · rw [show η (-1) = -1 from h]; ring
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψε]
      simp only [ε]
      linear_combination -hη2
    have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [sum_eq_single j] at hsum
    · rw [bracket_unit hpm hψ η (a j) hj, if_pos (by rw [hηc]; exact hfd)] at hsum
      have hw : (m.totient : ℂ) / (dm m (a j)).totient ≠ 0 :=
        div_ne_zero (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
          (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero hd0)).ne')
      have hψb : ψ (b : ZMod (p ^ r)) ≠ 0 := by
        rw [← ZMod.coe_unitOfCoprime b hbP]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
      have hηb := primChar_ne_zero η b hbf
      have he : (e j : ℂ) ≠ 0 := by exact_mod_cast hej
      rcases mul_eq_zero.1 hsum with h | h
      · exact absurd h he
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact absurd h hw
          · exact absurd h hψb
        · exact absurd h hηb
      · exact h
    · intro k _ hk
      by_cases hpk : p ∣ a k
      · rw [bracket_p_dvd hr hpm hψ η _ hpk, mul_zero]
      by_cases hek : e k = 0
      · rw [hek]; simp
      rw [bracket_unit hpm hψ η (a k) hpk, if_neg (by rw [hηc]; exact hiso k hk hpk hek), mul_zero]
    · intro h; exact absurd (mem_univ j) h
  have hc2 : (2 : ℕ).Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two hp.out).2 (by omega))
  set g2 : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime 2 hc2
  have hg2 : (g2 : ZMod (p ^ r)) = ((2 : ℕ) : ZMod (p ^ r)) := ZMod.coe_unitOfCoprime 2 hc2
  have hE : eulerPrimes d η.conductor ⊆ {2} := by
    intro ℓ hl; rw [hηc] at hl; exact mem_singleton.2 (euler_fpc hl)
  obtain ⟨h21, h2m1⟩ := two_ne_pm_one hP7
  rcases subset_singleton_iff.1 hE with h0 | h2
  · have := Erdos634.LemmaSG2.lemmaG hp7 hr hε g2 0 (fun ψ hψ hψε => by
      have := key ψ hψ hψε
      rw [h0, prod_empty] at this
      exact absurd this one_ne_zero)
    rw [hg2] at this
    rcases this with h | h
    · exact h21 h
    · exact h2m1 h
  · set c' := η.primitiveCharacter⁻¹ ((2 : ℕ) : ZMod η.conductor)
    have := Erdos634.LemmaSG2.lemmaG hp7 hr hε g2 c' (fun ψ hψ hψε => by
      have h := key ψ hψ hψε
      rw [h2, prod_singleton] at h
      have hψ2 : ψ (g2 : ZMod (p ^ r)) ≠ 0 := Erdos634.DirichletCRT.unit_val_ne_zero _ _
      rw [hg2] at hψ2 ⊢
      rw [MulChar.inv_apply_eq_inv'] at h
      have h' : (ψ ((2 : ℕ) : ZMod (p ^ r)))⁻¹ * c' = 1 := by linear_combination -h
      calc ψ ((2 : ℕ) : ZMod (p ^ r))
          = ψ ((2 : ℕ) : ZMod (p ^ r)) * ((ψ ((2 : ℕ) : ZMod (p ^ r)))⁻¹ * c') := by rw [h', mul_one]
        _ = c' := by rw [← mul_assoc, mul_inv_cancel₀ hψ2, one_mul])
    rw [hg2] at this
    rcases this with h | h
    · exact h21 h
    · exact h2m1 h
end Iso
end Erdos634.LemmaSIso
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSElim
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (dm)
open Erdos634.LemmaSIso (fpc lemmaIso fpc_dvd fpc_mod4 fpc_ne_zero)
def classSum {ι : Type*} [Fintype ι] (a : ι → ℕ) (e : ι → ℚ) (y : ℕ) : ℚ :=
  ∑ j ∈ univ.filter (fun j => a j = y), e j
theorem regroup {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n) (a : ι → ℕ) (e : ι → ℚ) :
    ∑ j, (e j : ℂ) * bracket χ (a j) =
      ∑ y : (univ.image a), ((classSum a e y : ℚ) : ℂ) * bracket χ y := by
  rw [sum_coe_sort (univ.image a) (fun y => ((classSum a e y : ℚ) : ℂ) * bracket χ y),
    ← sum_fiberwise_of_maps_to (g := a) (t := univ.image a)
      (fun j _ => mem_image_of_mem a (mem_univ j))]
  refine sum_congr rfl (fun y _ => ?_)
  unfold classSum
  rw [Rat.cast_sum, sum_mul]
  exact sum_congr rfl (fun j hj => by rw [(mem_filter.1 hj).2])
section Cls
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem lemmaIso_class (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ univ.image a) (hpx : ¬ p ∣ x)
    (hiso : ∀ y ∈ univ.image a, y ≠ x → ¬ p ∣ y → classSum a e y ≠ 0 →
      ¬ fpc (dm m x) ∣ dm m y) :
    classSum a e x = 0 := by
  have := lemmaIso (p := p) (r := r) (m := m) hp7 hr hpm (ι := univ.image a)
    (fun y => (y : ℕ)) (fun y => classSum a e y)
    (fun χ ho hc => by rw [← regroup χ a e]; exact hP χ ho hc) ⟨x, hx⟩ hpx
    (fun k hk hpk hek => hiso k k.2 (fun h => hk (Subtype.ext h)) hpk hek)
  exact this
theorem pp_dvd_dm {q k a : ℕ} (hq : q.Prime) (hqm : q ^ k ∣ m) (hqa : ¬ q ∣ a) :
    q ^ k ∣ dm m a := by
  have hc : (q ^ k).Coprime (m.gcd a) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2
      (fun h => hqa (dvd_trans h (Nat.gcd_dvd_right m a))))
  refine hc.dvd_of_dvd_mul_right ?_
  rw [dm, Nat.div_mul_cancel (Nat.gcd_dvd_left m a)]; exact hqm
theorem dvd_fpc {q k d : ℕ} (hqd : q ^ k ∣ d) (h2 : q ≠ 2 ∨ 2 ≤ k) (hq : q.Prime) :
    q ^ k ∣ fpc d := by
  unfold fpc
  split_ifs with h
  · rcases h2 with h2 | h2
    · have hc : (q ^ k).Coprime 2 :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).2 h2)
      refine hc.dvd_of_dvd_mul_left ?_
      rwa [Nat.mul_div_cancel' (show 2 ∣ d by omega)]
    · by_cases hq2 : q = 2
      · subst hq2
        have : 4 ∣ d := dvd_trans (by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 h2) hqd
        omega
      · have hc : (q ^ k).Coprime 2 :=
          Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
        refine hc.dvd_of_dvd_mul_left ?_
        rwa [Nat.mul_div_cancel' (show 2 ∣ d by omega)]
  · exact hqd
theorem deficiency {y : ℕ} (hnf : ¬ fpc m ∣ dm m y) :
    ∃ q k : ℕ, q.Prime ∧ 1 ≤ k ∧ q ^ k ∣ fpc m ∧ ¬ q ^ k ∣ dm m y ∧ (q ≠ 2 ∨ 2 ≤ k) := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hf0 : fpc m ≠ 0 := fpc_ne_zero hm0
  have hd0 : dm m y ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left m y)
    rw [show m / m.gcd y = 0 from h0, zero_mul] at this
    exact hm0 this.symm
  rw [← Nat.factorization_le_iff_dvd hf0 hd0, Finsupp.le_def] at hnf
  push_neg at hnf
  obtain ⟨q, hq⟩ := hnf
  have hqp : q.Prime := by
    by_contra hnp
    simp [Nat.factorization_eq_zero_of_not_prime _ hnp] at hq
  refine ⟨q, (fpc m).factorization q, hqp, by omega, Nat.ordProj_dvd _ _,
    fun h => by rw [hqp.pow_dvd_iff_le_factorization hd0] at h; omega, ?_⟩
  by_cases hq2 : q = 2
  · subst hq2
    right
    have h2 : 2 ∣ fpc m := by
      have := Nat.ordProj_dvd (fpc m) 2
      exact dvd_trans (dvd_pow_self 2 (by omega)) this
    have h4 : 2 ^ 2 ∣ fpc m := by have := fpc_mod4 m; norm_num; omega
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hf0).1 h4
  · exact Or.inl hq2
theorem not_two_dvd {a : Fin 3 → ℕ} (hgcd : univ.gcd a = 1) {q : ℕ} (hq : q.Prime)
    (hn : q ∣ a 0 + a 1 + a 2) {j k : Fin 3} (hjk : j ≠ k) (hj : q ∣ a j) (hk : q ∣ a k) : False := by
  have H : ∀ t : Fin 3, ((a t : ℕ) : ZMod q) = 0 := by
    have hs : ((a 0 : ZMod q) + a 1 + a 2) = 0 := by
      have := (ZMod.natCast_eq_zero_iff _ _).2 hn; push_cast at this; exact this
    have hj' := (ZMod.natCast_eq_zero_iff _ _).2 hj
    have hk' := (ZMod.natCast_eq_zero_iff _ _).2 hk
    intro t
    fin_cases j <;> fin_cases k <;> fin_cases t <;> simp at hjk hj' hk' ⊢ <;>
      first | exact hj' | exact hk' | linear_combination hs - hj' - hk'
  have : q ∣ univ.gcd a := Finset.dvd_gcd (fun t _ => (ZMod.natCast_eq_zero_iff _ _).1 (H t))
  rw [hgcd] at this
  exact hq.one_lt.ne' (Nat.dvd_one.1 this)
theorem lemmaElim (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hsum : a 0 + a 1 + a 2 = p ^ r * m) (hgcd : univ.gcd a = 1)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (hfull : ∀ x ∈ univ.image a, ¬ p ∣ x → fpc m ∣ dm m x → classSum a e x = 0) :
    ∀ x ∈ univ.image a, ¬ p ∣ x → classSum a e x = 0 := by
  intro z hz hpz
  by_cases hzf : fpc m ∣ dm m z
  · exact hfull z hz hpz hzf
  refine lemmaIso_class hp7 hr hpm a e hP z hz hpz (fun y hy hyz hpy hEy hdiv => ?_)
  have hyf : ¬ fpc m ∣ dm m y := fun h => hEy (hfull y hy hpy h)
  obtain ⟨q, k, hq, hk, hqf, hqy, h2⟩ := deficiency hyf
  have hqm : q ^ k ∣ m := dvd_trans hqf (fpc_dvd m)
  have hqa : q ∣ y := by
    by_contra h; exact hqy (pp_dvd_dm hq hqm h)
  have hqz : ¬ q ∣ z := by
    intro h
    obtain ⟨jy, -, rfl⟩ := mem_image.1 hy
    obtain ⟨jz, -, rfl⟩ := mem_image.1 hz
    have hne : jy ≠ jz := fun h' => hyz (by rw [h'])
    have hqn : q ∣ a 0 + a 1 + a 2 := by
      rw [hsum]; exact dvd_mul_of_dvd_right (dvd_trans (dvd_pow_self q (by omega)) hqm) _
    exact not_two_dvd hgcd hq hqn hne hqa h
  have := dvd_fpc (pp_dvd_dm hq hqm hqz) h2 hq
  exact hqy (dvd_trans this hdiv)
end Cls
end Erdos634.LemmaSElim
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSParity
open DirichletCharacter
open Erdos634.LemmaSGpp (sum_prim card_prim)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.DirichletCRT (isPrimitive_iff decomp)
theorem neg_one_eq_one_iff {N : ℕ} : (-1 : ZMod N) = 1 ↔ N ∣ 2 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h
def EP (d : ℕ) : Prop := ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ χ (-1) = 1
def OP (d : ℕ) : Prop := ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ χ (-1) = -1
section PP
variable {q v : ℕ} [hq : Fact q.Prime]
theorem pp_counts (hv : 1 ≤ v) :
    ∃ E O : ℕ, (0 < E ↔ EP (q ^ v)) ∧ (0 < O ↔ OP (q ^ v)) ∧
      E + O + (q ^ (v - 1)).totient = (q ^ v).totient ∧
      (E : ℂ) - O = (if q ^ v ∣ 2 then ((q ^ v).totient : ℂ) else 0) -
        (if q ^ (v - 1) ∣ 2 then ((q ^ (v - 1)).totient : ℂ) else 0) := by
  classical
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  set Pr := univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)
  set Ev := Pr.filter (fun χ => χ (-1) = 1)
  set Od := Pr.filter (fun χ => ¬ χ (-1) = 1)
  have hsplit := card_filter_add_card_filter_not (s := Pr) (fun χ => χ (-1) = 1)
  have hodd : ∀ χ ∈ Od, χ (-1) = -1 := by
    intro χ hχ
    exact (Erdos634.LemmaSG.val_neg_one χ).resolve_left (mem_filter.1 hχ).2
  refine ⟨Ev.card, Od.card, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h; obtain ⟨χ, hχ⟩ := card_pos.1 h
      exact ⟨χ, (mem_filter.1 (mem_filter.1 hχ).1).2, (mem_filter.1 hχ).2⟩
    · rintro ⟨χ, hp, he⟩
      exact card_pos.2 ⟨χ, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hp⟩, he⟩⟩
  · constructor
    · intro h; obtain ⟨χ, hχ⟩ := card_pos.1 h
      exact ⟨χ, (mem_filter.1 (mem_filter.1 hχ).1).2, hodd χ hχ⟩
    · rintro ⟨χ, hp, ho⟩
      refine card_pos.2 ⟨χ, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hp⟩, ?_⟩⟩
      rw [ho]; norm_num
  · rw [hsplit]; exact card_prim hv
  · have hS := sum_prim hv (-1 : (ZMod (q ^ v))ˣ)
    rw [← sum_filter_add_sum_filter_not Pr (fun χ => χ (-1) = 1)] at hS
    simp only [Units.val_neg, Units.val_one] at hS
    rw [sum_congr rfl (fun χ hχ => (mem_filter.1 hχ).2),
      sum_congr rfl (fun χ hχ => hodd χ hχ), sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul] at hS
    simp only [ZMod.cast_neg (pred_dvd q v), ZMod.cast_one (pred_dvd q v), neg_one_eq_one_iff] at hS
    linear_combination hS
theorem pp_parity (hv : 1 ≤ v) (h2 : q ^ v ≠ 2) :
    (EP (q ^ v) ↔ q ^ v ≠ 3 ∧ q ^ v ≠ 4) ∧ OP (q ^ v) := by
  obtain ⟨E, O, hE, hO, hsum, hdiff⟩ := pp_counts (q := q) hv
  have hq2 := hq.out.two_le
  have hqv : 2 ≤ q ^ v := le_trans hq2 (Nat.le_self_pow (by omega) q)
  rw [if_neg (fun h => h2 (le_antisymm (Nat.le_of_dvd (by norm_num) h) hqv))] at hdiff
  have hpow : q ^ v = q ^ (v - 1) * q := by rw [← pow_succ]; congr 1; omega
  have htot : (q ^ v).totient = q ^ (v - 1) * (q - 1) := by
    rw [Nat.totient_prime_pow hq.out (by omega)]
  by_cases hd2 : q ^ (v - 1) ∣ 2
  · rw [if_pos hd2] at hdiff
    have hN : q ^ (v - 1) = 1 ∨ q ^ (v - 1) = 2 := by
      have := Nat.le_of_dvd (by norm_num) hd2
      have := Nat.pos_of_ne_zero (pow_ne_zero (v - 1) hq.out.ne_zero)
      omega
    have hD : (q ^ (v - 1)).totient = 1 := by
      rcases hN with h | h <;> rw [h] <;> decide
    rw [hD] at hdiff hsum
    have hEO : E + 1 = O := by
      have : ((E + 1 : ℕ) : ℂ) = O := by push_cast; linear_combination hdiff
      exact_mod_cast this
    refine ⟨?_, hO.1 (by omega)⟩
    rw [← hE]
    rcases hN with h | h
    · rw [h, one_mul] at hpow htot
      rw [hpow]
      constructor
      · intro hE0; constructor <;> omega
      · rintro ⟨h3, h4⟩; omega
    · have hq2' : q = 2 := by
        have hv1 : 1 ≤ v - 1 := by
          by_contra hc; have : v - 1 = 0 := by omega
          rw [this, pow_zero] at h; omega
        have : q ∣ 2 := h ▸ dvd_pow_self q (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 this
      subst hq2'
      rw [h] at hpow htot
      rw [hpow]
      constructor
      · intro hE0; omega
      · rintro ⟨-, h4⟩; exact absurd rfl h4
  · rw [if_neg hd2, sub_zero] at hdiff
    have hEO : E = O := by exact_mod_cast (sub_eq_zero.1 hdiff)
    have hD0 : 0 < (q ^ (v - 1)).totient := Nat.totient_pos.2 (pow_pos hq.out.pos _)
    have hlt := Erdos634.LemmaSGpp.totient_lt (q := q) hv h2
    have hpos : 0 < E := by omega
    refine ⟨⟨fun _ => ⟨?_, ?_⟩, fun _ => hE.1 hpos⟩, hO.1 (by omega)⟩
    · intro h3
      have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_three).1
        (h3 ▸ dvd_pow_self q (by omega))
      subst hq3
      have hv1 : v = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3)
        (show 3 ^ v = 3 ^ 1 by rw [h3])
      subst hv1; exact hd2 (by simp)
    · intro h4
      have hq2' : q = 2 := by
        have : q ∣ 2 ^ 2 := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]; exact dvd_pow_self q (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 (hq.out.dvd_of_dvd_pow this)
      subst hq2'
      have hv2 : v = 2 := Nat.pow_right_injective (le_refl 2)
        (show 2 ^ v = 2 ^ 2 by rw [h4])
      subst hv2; exact hd2 (by norm_num)
end PP
theorem prod_neg_one {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] (ψ : DirichletCharacter ℂ m₁)
    (η : DirichletCharacter ℂ m₂) :
    (changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η) (-1) =
      ψ (-1) * η (-1) := by
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  rw [MulChar.coeToFun_mul, Pi.mul_apply, Erdos634.LemmaSG2.changeLevel_neg_one,
    Erdos634.LemmaSG2.changeLevel_neg_one]
theorem EP_mul {a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b) :
    EP (a * b) ↔ (EP a ∧ EP b) ∨ (OP a ∧ OP b) := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  constructor
  · rintro ⟨χ, hp, he⟩
    have e := decomp h χ
    obtain ⟨p1, p2⟩ := (isPrimitive_iff h e).1 hp
    rw [e, prod_neg_one] at he
    rcases Erdos634.LemmaSG.val_neg_one (Erdos634.DirichletCRT.comp₁ h χ) with h1 | h1 <;>
      rcases Erdos634.LemmaSG.val_neg_one (Erdos634.DirichletCRT.comp₂ h χ) with h2 | h2 <;>
      rw [h1, h2] at he <;> norm_num at he
    · exact Or.inl ⟨⟨_, p1, h1⟩, ⟨_, p2, h2⟩⟩
    · exact Or.inr ⟨⟨_, p1, h1⟩, ⟨_, p2, h2⟩⟩
  · rintro (⟨⟨ψ, hψ, h1⟩, ⟨η, hη, h2⟩⟩ | ⟨⟨ψ, hψ, h1⟩, ⟨η, hη, h2⟩⟩)
    · exact ⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩, by rw [prod_neg_one, h1, h2, one_mul]⟩
    · exact ⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩, by rw [prod_neg_one, h1, h2]; norm_num⟩
theorem OP_mul {a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b) :
    OP (a * b) ↔ (EP a ∧ OP b) ∨ (OP a ∧ EP b) := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  constructor
  · rintro ⟨χ, hp, ho⟩
    have e := decomp h χ
    obtain ⟨p1, p2⟩ := (isPrimitive_iff h e).1 hp
    rw [e, prod_neg_one] at ho
    rcases Erdos634.LemmaSG.val_neg_one (Erdos634.DirichletCRT.comp₁ h χ) with h1 | h1 <;>
      rcases Erdos634.LemmaSG.val_neg_one (Erdos634.DirichletCRT.comp₂ h χ) with h2 | h2 <;>
      rw [h1, h2] at ho <;> norm_num at ho
    · exact Or.inl ⟨⟨_, p1, h1⟩, ⟨_, p2, h2⟩⟩
    · exact Or.inr ⟨⟨_, p1, h1⟩, ⟨_, p2, h2⟩⟩
  · rintro (⟨⟨ψ, hψ, h1⟩, ⟨η, hη, h2⟩⟩ | ⟨⟨ψ, hψ, h1⟩, ⟨η, hη, h2⟩⟩)
    · exact ⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩, by rw [prod_neg_one, h1, h2, one_mul]⟩
    · exact ⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩, by rw [prod_neg_one, h1, h2, mul_one]⟩
theorem ne_twelve_of_pp {p n : ℕ} (hp : p.Prime) : p ^ n ≠ 12 := by
  intro h
  have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (show 3 ∣ p ^ n by rw [h]; norm_num)
  have hp3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
  subst hp3
  have : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ 3 ^ n by rw [h]; norm_num)
  norm_num at this
def Stmt (d : ℕ) : Prop :=
  d ≠ 0 → d % 4 ≠ 2 → (EP d ↔ d ≠ 3 ∧ d ≠ 4) ∧ (OP d ↔ d ≠ 1 ∧ d ≠ 12)
theorem mod4_left {a b : ℕ} (h : a.Coprime b) (hab : (a * b) % 4 ≠ 2) : a % 4 ≠ 2 :=
  Erdos634.LemmaSGprime.mod4_left h hab
theorem stmt_all (d : ℕ) : Stmt d := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ _
    have h1 : ∀ χ : DirichletCharacter ℂ 1, χ (-1) = 1 := by
      intro χ; rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
    refine ⟨⟨fun _ => by norm_num, fun _ => ⟨1, isPrimitive_one_level_one, h1 1⟩⟩, ?_⟩
    constructor
    · rintro ⟨χ, -, h⟩; rw [h1 χ] at h; norm_num at h
    · rintro ⟨h, -⟩; exact absurd rfl h
  | prime_pow p n hp hn =>
    intro _ h4
    haveI : Fact p.Prime := ⟨hp⟩
    have h2 : p ^ n ≠ 2 := fun e => h4 (by rw [e])
    obtain ⟨hE, hO⟩ := pp_parity (q := p) (v := n) hn h2
    refine ⟨hE, ⟨fun _ => ⟨?_, ne_twelve_of_pp hp⟩, fun _ => hO⟩⟩
    exact (Nat.one_lt_pow hn.ne' hp.one_lt).ne'
  | coprime a b ha hb h IHa IHb =>
    intro _ h4
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    obtain ⟨Ea, Oa⟩ := IHa (by omega) (mod4_left h h4)
    obtain ⟨Eb, Ob⟩ := IHb (by omega) (mod4_left h.symm (by rwa [mul_comm]))
    rw [EP_mul h, OP_mul h, Ea, Oa, Eb, Ob]
    have hcop : Nat.gcd a b = 1 := h
    have h6 : 6 ≤ a * b := by
      rcases Nat.lt_or_ge a 3 with h' | h'
      · obtain rfl : a = 2 := by omega
        rcases Nat.lt_or_ge b 3 with h'' | h''
        · obtain rfl : b = 2 := by omega
          norm_num at hcop
        · omega
      · nlinarith
    have k12 : a * b = 12 → (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) := by
      intro h12
      have ha12 : a ≤ 12 := Nat.le_of_dvd (by norm_num) ⟨b, h12.symm⟩
      have hb12 : b ≤ 12 := Nat.le_of_dvd (by norm_num) ⟨a, by rw [mul_comm]; exact h12.symm⟩
      interval_cases a <;> interval_cases b <;> first | omega | (norm_num at hcop)
    constructor
    · have hne : a * b ≠ 3 ∧ a * b ≠ 4 := by omega
      refine ⟨fun _ => hne, fun _ => ?_⟩
      by_cases ha : a = 3 ∨ a = 4
      · right; refine ⟨⟨by omega, by omega⟩, ⟨by omega, ?_⟩⟩
        rintro rfl; rcases ha with rfl | rfl <;> norm_num at hcop
      · by_cases hb' : b = 3 ∨ b = 4
        · right; refine ⟨⟨by omega, ?_⟩, ⟨by omega, by omega⟩⟩
          rintro rfl; rcases hb' with rfl | rfl <;> norm_num at hcop
        · left; omega
    · by_cases h12 : a * b = 12
      · rcases k12 h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
      · refine ⟨fun _ => ⟨by omega, h12⟩, fun _ => ?_⟩
        by_cases ha : a = 3 ∨ a = 4
        · right; refine ⟨⟨by omega, by omega⟩, ?_⟩
          by_contra hb'
          have hb34 : b = 3 ∨ b = 4 := by omega
          apply h12
          rcases ha with rfl | rfl <;> rcases hb34 with rfl | rfl <;>
            first | (exfalso; norm_num at hcop; done) | norm_num
        · by_cases hb12 : b = 12
          · right; subst hb12; refine ⟨⟨by omega, ?_⟩, by omega⟩
            rintro rfl; norm_num at hcop
          · left; omega
theorem exists_even_primitive_iff {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 ≠ 2) :
    (∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ χ.Even) ↔ d ≠ 3 ∧ d ≠ 4 :=
  (stmt_all d hd0 hd).1
end Erdos634.LemmaSParity
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSFC
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit primChar_nat_of_isPrimitive sum_indicator)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSN (pred_dvd lemmaN_a lemmaN_b)
section FC
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem dm_eq_iff (y : ℕ) : dm m y = m ↔ y.Coprime m := by
  rw [dm, Nat.div_eq_self]
  simp only [NeZero.ne m, false_or]
  exact ⟨fun h => Nat.coprime_comm.1 h, fun h => Nat.coprime_comm.1 h⟩
theorem fc_term (hpm : ¬ p ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)} (hψ : ψ.IsPrimitive)
    {η : DirichletCharacter ℂ m} (hη : η.IsPrimitive) (y : ℕ) (hy : ¬ p ∣ y) :
    bracket (chi ψ η) y = if y.Coprime m then ψ (y : ZMod (p ^ r)) * η (y : ZMod m) else 0 := by
  have hc : η.conductor = m := hη
  rw [bracket_unit hpm hψ η y hy]
  by_cases hcop : y.Coprime m
  · have hdm : dm m y = m := (dm_eq_iff y).2 hcop
    have hg : m.gcd y = 1 := Nat.coprime_comm.1 hcop
    rw [if_pos (by rw [hc, hdm]), if_pos hcop, hg, Nat.div_one, hdm]
    have hE : eulerPrimes m η.conductor = ∅ := by
      rw [hc]; ext ℓ
      simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
      rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
    rw [hE, prod_empty, primChar_nat_of_isPrimitive hη,
      div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')]
    ring
  · rw [if_neg hcop, if_neg]
    intro h
    rw [hc] at h
    exact hcop ((dm_eq_iff y).1 (Nat.dvd_antisymm (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m y)) h))
def fullPts {ι : Type*} [Fintype ι] [DecidableEq ι] (p m : ℕ) (a : ι → ℕ) : Finset ℕ :=
  (univ.image a).filter (fun y => ¬ p ∣ y ∧ y.Coprime m)
theorem fc_component (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)}
    (hψ : ψ.IsPrimitive) {η : DirichletCharacter ℂ m} (hη : η.IsPrimitive) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ) :
    ∑ j, (e j : ℂ) * bracket (chi ψ η) (a j) =
      ∑ y ∈ fullPts p m a, ((classSum a e y : ℚ) : ℂ) * (ψ (y : ZMod (p ^ r)) * η (y : ZMod m)) := by
  rw [regroup, sum_coe_sort (univ.image a)
    (fun y => ((classSum a e y : ℚ) : ℂ) * bracket (chi ψ η) y), fullPts, sum_filter]
  refine sum_congr rfl (fun y _ => ?_)
  by_cases hpy : p ∣ y
  · rw [bracket_p_dvd hr hpm hψ η y hpy, if_neg (fun h => h.1 hpy), mul_zero]
  · rw [fc_term hpm hψ hη y hpy]
    by_cases hcop : y.Coprime m
    · rw [if_pos hcop, if_pos ⟨hpy, hcop⟩]
    · rw [if_neg hcop, if_neg (fun h => hcop h.2), mul_zero]
noncomputable def PhiF {ι : Type*} [Fintype ι] [DecidableEq ι] (p r m : ℕ)
    (η : DirichletCharacter ℂ m) (a : ι → ℕ) (e : ι → ℚ) (u : (ZMod (p ^ r))ˣ) : ℂ :=
  ∑ y ∈ fullPts p m a, if (u : ZMod (p ^ r)) = y then ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) else 0
theorem psi_PhiF (ψ : DirichletCharacter ℂ (p ^ r)) (η : DirichletCharacter ℂ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ) :
    ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * PhiF p r m η a e u =
      ∑ y ∈ fullPts p m a, ((classSum a e y : ℚ) : ℂ) * (ψ (y : ZMod (p ^ r)) * η (y : ZMod m)) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  unfold PhiF
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun y _ => ?_)
  have := sum_indicator ψ 1 (y : ZMod (p ^ r)) isUnit_one
  rw [map_one, inv_one, mul_one] at this
  calc _ = ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) * ∑ u : (ZMod (p ^ r))ˣ,
        ψ (u : ZMod (p ^ r)) * (if (u : ZMod (p ^ r)) * 1 = y then 1 else 0) := by
          rw [mul_sum]; refine sum_congr rfl (fun u _ => ?_)
          rw [mul_one]; split_ifs <;> ring
    _ = _ := by rw [this]; ring
theorem card_val_le_one {N : ℕ} [NeZero N] (x : ZMod N) :
    (univ.filter (fun v : (ZMod N)ˣ => (v : ZMod N) = x)).card ≤ 1 :=
  card_le_one.2 (fun v hv w hw => Units.ext ((mem_filter.1 hv).2.trans (mem_filter.1 hw).2.symm))
theorem fc_symm (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    {η : DirichletCharacter ℂ m} (hη : η.IsPrimitive)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    ∀ u, PhiF p r m η a e u = η (-1) * PhiF p r m η a e (-u) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set ε : ℂ := -η (-1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases η.even_or_odd with h | h
    · right; simp only [ε, show η (-1) = 1 from h]
    · left; simp only [ε, show η (-1) = -1 from h, neg_neg]
  have hη2 : η (-1) * η (-1) = 1 := by
    rcases η.even_or_odd with h | h
    · rw [show η (-1) = 1 from h]; ring
    · rw [show η (-1) = -1 from h]; ring
  set Φ := PhiF p r m η a e
  have hΦ : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0 := by
    intro ψ hψ hψε
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψε]
      simp only [ε]; linear_combination -hη2
    have h0 := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [fc_component hr hpm hψ hη a e] at h0
    rw [psi_PhiF]; exact h0
  have hS : ∀ v : (ZMod (p ^ r))ˣ, Φ v ≠ 0 → ∃ y ∈ fullPts p m a, (v : ZMod (p ^ r)) = y := by
    intro v hv
    by_contra hno
    push Not at hno
    exact hv (sum_eq_zero (fun y hy => if_neg (hno y hy)))
  have hcount : ∀ u : (ZMod (p ^ r))ˣ,
      (univ.filter (fun v => ZMod.unitsMap (pred_dvd p r) v = ZMod.unitsMap (pred_dvd p r) u ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0))).card
        < (univ.filter (fun v => ZMod.unitsMap (pred_dvd p r) v = 1)).card := by
    intro u
    refine lt_of_le_of_lt ?_ hN
    calc _ ≤ (((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).biUnion (fun t =>
            univ.filter (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)) = t) ∪
            univ.filter (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)) = -t))).card := by
          refine card_le_card (fun v hv => ?_)
          rcases (mem_filter.1 hv).2.2 with h | h
          · obtain ⟨y, hy, hvy⟩ := hS v h
            exact mem_biUnion.2 ⟨_, mem_image_of_mem _ hy,
              mem_union_left _ (mem_filter.2 ⟨mem_univ _, hvy⟩)⟩
          · obtain ⟨y, hy, hvy⟩ := hS (-v) h
            refine mem_biUnion.2 ⟨_, mem_image_of_mem _ hy,
              mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)⟩
            rw [Units.val_neg] at hvy; rw [← hvy, neg_neg]
      _ ≤ ∑ t ∈ (fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r))), 2 := by
          refine card_biUnion_le.trans (sum_le_sum (fun t _ => ?_))
          exact (card_union_le _ _).trans (by
            have := card_val_le_one (N := p ^ r) t
            have := card_val_le_one (N := p ^ r) (-t)
            omega)
      _ = 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
  intro u
  rw [lemmaN_a hr Φ hε hΦ hcount u]
  simp only [ε, neg_neg]
theorem fc_isolated_img (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ fullPts p m a)
    (hsep : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ r)) ≠ x ∧ (y : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    classSum a e x = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨η, hη⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne m) hm4
  set Φ := PhiF p r m η a e
  have hN' : ∀ u, Φ u = η (-1) * Φ (-u) := fc_symm hr hpm a e hP hη hN
  have hxf := mem_filter.1 hx
  have hxP : x.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  set ux : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime x hxP
  have hux : (ux : ZMod (p ^ r)) = x := ZMod.coe_unitOfCoprime x hxP
  have hxx : (x : ZMod (p ^ r)) ≠ -x := by
    intro h
    have h2 : ((2 * x : ℕ) : ZMod (p ^ r)) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.Prime.dvd_mul hp.out).1 (dvd_trans (dvd_pow_self p (by omega)) h2)
    rcases this with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hxf.2.1 h
  have hv1 : Φ ux = ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) := by
    simp only [Φ, PhiF]
    rw [sum_eq_single x]
    · rw [if_pos hux]
    · intro y hy hyx
      by_cases hE : classSum a e y = 0
      · split_ifs <;> simp [hE]
      · rw [if_neg]; rw [hux]; exact fun h => (hsep y hy hyx hE).1 h.symm
    · intro h; exact absurd hx h
  have hv2 : Φ (-ux) = 0 := by
    simp only [Φ, PhiF]
    refine sum_eq_zero (fun y hy => ?_)
    rw [Units.val_neg, hux]
    by_cases hyx : y = x
    · subst hyx; rw [if_neg (fun h => hxx h.symm)]
    by_cases hE : classSum a e y = 0
    · split_ifs <;> simp [hE]
    · rw [if_neg]; exact fun h => (hsep y hy hyx hE).2 h.symm
  have := hN' ux
  rw [hv1, hv2, mul_zero] at this
  have hηx : η (x : ZMod m) ≠ 0 := by
    rw [← ZMod.coe_unitOfCoprime x hxf.2.2]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  exact_mod_cast (mul_eq_zero.1 this).resolve_right hηx
theorem fc_isolated (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ fullPts p m a)
    (hsep : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ r)) ≠ x ∧ (y : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * (fullPts p m a).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    classSum a e x = 0 :=
  fc_isolated_img hp7 hr hpm hm4 a e hP x hx hsep
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 card_image_le) hN)
theorem fc_isolated_even (hp7 : 7 ≤ p) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2) (hm34 : m ≠ 3 ∧ m ≠ 4)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ 1 * m), χ.Odd → p ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ fullPts p m a)
    (hsep : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ 1)) ≠ x ∧ (y : ZMod (p ^ 1)) ≠ -x) :
    classSum a e x = 0 := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨η, hη, hev⟩ :=
    (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne m) hm4).2 hm34
  set Φ := PhiF p 1 m η a e
  have hΦ : ∀ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (p ^ 1))ˣ, ψ (u : ZMod (p ^ 1)) * Φ u = 0 := by
    intro ψ hψ hψε
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ 1) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ 1)) η, hψε,
        show η (-1) = 1 from hev, mul_one]
    have h0 := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [fc_component le_rfl hpm hψ hη a e] at h0
    rw [psi_PhiF]; exact h0
  have hN' := lemmaN_b Φ hΦ
  have hxf := mem_filter.1 hx
  have hxP : x.Coprime (p ^ 1) :=
    Nat.Coprime.pow_right 1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  set ux : (ZMod (p ^ 1))ˣ := ZMod.unitOfCoprime x hxP
  have hux : (ux : ZMod (p ^ 1)) = x := ZMod.coe_unitOfCoprime x hxP
  have hxx : (x : ZMod (p ^ 1)) ≠ -x := by
    intro h
    have h2 : ((2 * x : ℕ) : ZMod (p ^ 1)) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.Prime.dvd_mul hp.out).1 (dvd_trans (dvd_pow_self p (by omega)) h2)
    rcases this with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hxf.2.1 h
  have hv1 : Φ ux = ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) := by
    simp only [Φ, PhiF]
    rw [sum_eq_single x]
    · rw [if_pos hux]
    · intro y hy hyx
      by_cases hE : classSum a e y = 0
      · split_ifs <;> simp [hE]
      · rw [if_neg]; rw [hux]; exact fun h => (hsep y hy hyx hE).1 h.symm
    · intro h; exact absurd hx h
  have hv2 : Φ (-ux) = 0 := by
    simp only [Φ, PhiF]
    refine sum_eq_zero (fun y hy => ?_)
    rw [Units.val_neg, hux]
    by_cases hyx : y = x
    · subst hyx; rw [if_neg (fun h => hxx h.symm)]
    by_cases hE : classSum a e y = 0
    · split_ifs <;> simp [hE]
    · rw [if_neg]; exact fun h => (hsep y hy hyx hE).2 h.symm
  have := hN' ux
  rw [hv1, hv2] at this
  have hηx : η (x : ZMod m) ≠ 0 := by
    rw [← ZMod.coe_unitOfCoprime x hxf.2.2]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  exact_mod_cast (mul_eq_zero.1 this).resolve_right hηx
theorem card_N (hr : 1 ≤ r) :
    (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card =
      if r = 1 then p - 1 else p := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (p ^ (r - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h := Erdos634.LemmaSC.fiber_card (pred_dvd p r)
  have hT0 : ((p ^ (r - 1)).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (pow_pos hp.out.pos _)).ne'
  rw [eq_div_iff hT0] at h
  have hnat : (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card *
      (p ^ (r - 1)).totient = (p ^ r).totient := by exact_mod_cast h
  have hT0' : 0 < (p ^ (r - 1)).totient := Nat.totient_pos.2 (pow_pos hp.out.pos _)
  split_ifs with h1
  · subst h1
    simp only [Nat.sub_self, pow_zero, Nat.totient_one, mul_one, pow_one,
      Nat.totient_prime hp.out] at hnat
    exact hnat
  · have htot : (p ^ r).totient = p * (p ^ (r - 1)).totient := by
      rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]
      exact Nat.totient_mul_of_prime_of_dvd hp.out (dvd_pow_self p (by omega))
    rw [htot] at hnat
    exact Nat.eq_of_mul_eq_mul_right hT0' hnat
theorem fc_generic (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (hcase : 11 ≤ p ∨ 2 ≤ r ∨ (fullPts p m a).card ≤ 2 ∨ (r = 1 ∧ m ≠ 3 ∧ m ≠ 4))
    (x : ℕ) (hx : x ∈ fullPts p m a)
    (hsep : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ r)) ≠ x ∧ (y : ZMod (p ^ r)) ≠ -x) :
    classSum a e x = 0 := by
  have h3 : (fullPts p m a).card ≤ 3 :=
    (card_filter_le _ _).trans ((card_image_le).trans (by simp))
  rcases hcase with hc | hc | hc | ⟨rfl, hm34⟩
  rotate_left 3
  · exact fc_isolated_even hp7 hpm hm4 hm34 a e hP x hx hsep
  all_goals refine fc_isolated hp7 hr hpm hm4 a e hP x hx hsep ?_
  all_goals rw [card_N hr]
  all_goals split_ifs with h1 <;> omega
end FC
end Erdos634.LemmaSFC
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSL
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit changeLevel_nat)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSFC (fullPts PhiF fc_symm dm_eq_iff)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau lemmaG' Sp_mul tau_mul Sp_pp tau_pp)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive two_ne_pm_one)
theorem rel_Gprime {d : ℕ} [NeZero d] (hd4 : d % 4 ≠ 2) (Ex Ey : ℚ) (x y : ℕ) (hx : x.Coprime d)
    (hy : y.Coprime d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (z : ℤ) (hz : z * (σ * y) ≡ x [ZMOD d])
    (hrel : ∀ η : DirichletCharacter ℂ d, η.IsPrimitive →
      (Ex : ℂ) * η (x : ZMod d) + (σ : ℂ) * Ey * η (((σ * y : ℤ)) : ZMod d) = 0) :
    (Ex = 0 ∧ Ey = 0) ∨ (Sp d z ∧ Ey = -σ * (-1) ^ tau d z * Ex) := by
  obtain ⟨η0, hη0⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne d) hd4
  have hxu : IsUnit ((x : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime x d).2 hx
  have hyu : IsUnit ((y : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime y d).2 hy
  have hsy : IsUnit (((σ * y : ℤ)) : ZMod d) := by
    rcases hσ with rfl | rfl
    · rw [show (((1 * y : ℤ)) : ZMod d) = (y : ZMod d) by push_cast; ring]; exact hyu
    · rw [show (((-1 * y : ℤ)) : ZMod d) = -(y : ZMod d) by push_cast; ring]; exact hyu.neg
  have hσ2 : (σ : ℂ) * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : (σ : ℂ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨uy, huy⟩ := hsy
  obtain ⟨ux, hux⟩ := hxu
  have hne : ∀ η : DirichletCharacter ℂ d, η (((σ * y : ℤ)) : ZMod d) ≠ 0 := by
    intro η; rw [← huy]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  by_cases hEx : Ex = 0
  · left
    refine ⟨hEx, ?_⟩
    have := hrel η0 hη0
    rw [hEx, Rat.cast_zero, zero_mul, zero_add] at this
    have h2 := (mul_eq_zero.1 this).resolve_right (hne η0)
    exact_mod_cast (mul_eq_zero.1 h2).resolve_left hσ0
  · right
    set g : (ZMod d)ˣ := ux * uy⁻¹
    have hzg : ((z : ℤ) : ZMod d) = g := by
      have h1 : ((z : ℤ) : ZMod d) * (((σ * y : ℤ)) : ZMod d) = (x : ZMod d) := by
        have := (ZMod.intCast_eq_intCast_iff (z * (σ * y)) x d).2 hz
        rw [Int.cast_mul, Int.cast_natCast] at this; exact this
      have hyy : (((σ * y : ℤ)) : ZMod d) * ((uy⁻¹ : (ZMod d)ˣ) : ZMod d) = 1 := by
        rw [← huy, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc ((z : ℤ) : ZMod d)
          = ((z : ℤ) : ZMod d) * (((σ * y : ℤ)) : ZMod d) * ((uy⁻¹ : (ZMod d)ˣ) : ZMod d) := by
            rw [mul_assoc, hyy, mul_one]
        _ = _ := by rw [h1, ← hux, ← Units.val_mul]
    have hEx' : ((Ex : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hEx
    have hval : ∀ η : DirichletCharacter ℂ d, η.IsPrimitive → η (g : ZMod d) = -(σ : ℂ) * Ey / Ex := by
      intro η hη
      have hk := hrel η hη
      have hinv : η ((uy⁻¹ : (ZMod d)ˣ) : ZMod d) * η (((σ * y : ℤ)) : ZMod d) = 1 := by
        rw [← huy, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      rw [eq_div_iff hEx']
      simp only [g, Units.val_mul, map_mul, hux]
      linear_combination η ((uy⁻¹ : (ZMod d)ˣ) : ZMod d) * hk - (σ : ℂ) * Ey * hinv
    obtain ⟨G1, G2⟩ := lemmaG' (NeZero.ne d) hd4 g z hzg
    have hSp : Sp d z := G1.1 ⟨_, hval⟩
    refine ⟨hSp, ?_⟩
    have h := G2 hSp η0 hη0
    rw [hval η0 hη0, div_eq_iff hEx'] at h
    have : ((Ey : ℚ) : ℂ) = ((-σ * (-1) ^ tau d z * Ex : ℚ) : ℂ) := by
      push_cast; linear_combination (-(σ : ℂ)) * h - (Ey : ℂ) * hσ2
    exact_mod_cast this
section L
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem fc_key (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hβ : (y : ZMod (p ^ r)) = (σ : ZMod (p ^ r)) * x)
    (hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    ∀ η : DirichletCharacter ℂ m, η.IsPrimitive →
      ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) +
        (σ : ℂ) * (classSum a e y : ℚ) * η (((σ * y : ℤ)) : ZMod m) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro η hη
  have hxf := mem_filter.1 hx
  have hxP : x.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  set ux : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime x hxP
  have hux : (ux : ZMod (p ^ r)) = x := ZMod.coe_unitOfCoprime x hxP
  have hxx : (x : ZMod (p ^ r)) ≠ -x := by
    intro h
    have h2 : ((2 * x : ℕ) : ZMod (p ^ r)) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.Prime.dvd_mul hp.out).1 (dvd_trans (dvd_pow_self p (by omega)) h2)
    rcases this with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hxf.2.1 h
  have hs := fc_symm hr hpm a e hP hη hN ux
  have hzero : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → ∀ t : ZMod (p ^ r), (t = x ∨ t = -x) →
      (if t = (w : ZMod (p ^ r)) then ((classSum a e w : ℚ) : ℂ) * η (w : ZMod m) else 0) = 0 := by
    intro w hw hwx hwy t ht
    by_cases hE : classSum a e w = 0
    · split_ifs <;> simp [hE]
    · rw [if_neg]
      rcases ht with rfl | rfl
      · exact fun h => (hsep w hw hwx hwy hE).1 h.symm
      · exact fun h => (hsep w hw hwx hwy hE).2 h.symm
  rcases hσ with rfl | rfl
  · 
    have hβ' : (y : ZMod (p ^ r)) = x := by rw [hβ]; push_cast; ring
    have h1 : PhiF p r m η a e ux =
        ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) + ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) := by
      unfold PhiF
      rw [sum_eq_add_of_mem x y hx hy hxy]
      · rw [if_pos hux, if_pos (by rw [hux, hβ'])]
      · intro w hw ⟨hwx, hwy⟩; rw [hux]; exact hzero w hw hwx hwy _ (Or.inl rfl)
    have h2 : PhiF p r m η a e (-ux) = 0 := by
      unfold PhiF
      refine sum_eq_zero (fun w hw => ?_)
      rw [Units.val_neg, hux]
      by_cases hwx : w = x
      · subst hwx; rw [if_neg (fun h => hxx h.symm)]
      by_cases hwy : w = y
      · subst hwy; rw [if_neg (fun h => hxx (by rw [h, hβ']))]
      exact hzero w hw hwx hwy _ (Or.inr rfl)
    rw [h1, h2, mul_zero] at hs
    rw [show (((1 * y : ℤ)) : ZMod m) = (y : ZMod m) by push_cast; ring]
    push_cast; linear_combination hs
  · 
    have hβ' : (y : ZMod (p ^ r)) = -x := by rw [hβ]; push_cast; ring
    have hyx : (y : ZMod (p ^ r)) ≠ x := fun h => hxx (h.symm.trans hβ')
    have h1 : PhiF p r m η a e ux = ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) := by
      unfold PhiF
      rw [sum_eq_single x]
      · rw [if_pos hux]
      · intro w hw hwx
        rw [hux]
        by_cases hwy : w = y
        · subst hwy; rw [if_neg (fun h => hyx h.symm)]
        exact hzero w hw hwx hwy _ (Or.inl rfl)
      · intro h; exact absurd hx h
    have h2 : PhiF p r m η a e (-ux) = ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) := by
      unfold PhiF
      rw [sum_eq_single y]
      · rw [Units.val_neg, hux, if_pos hβ'.symm]
      · intro w hw hwy
        rw [Units.val_neg, hux]
        by_cases hwx : w = x
        · subst hwx; rw [if_neg (fun h => hxx h.symm)]
        exact hzero w hw hwx hwy _ (Or.inr rfl)
      · intro h; exact absurd hy h
    rw [h1, h2] at hs
    have hm1 : η (((-1 * y : ℤ)) : ZMod m) = η (-1) * η (y : ZMod m) := by
      rw [← map_mul]; congr 1; push_cast; ring
    rw [hm1]; push_cast; linear_combination hs
theorem primChar_lift {f : ℕ} [NeZero f] (h : f ∣ m) (η₀ : DirichletCharacter ℂ f) (b : ℕ)
    (hb : b.Coprime m) :
    (changeLevel h η₀).primitiveCharacter (b : ZMod (changeLevel h η₀).conductor) = η₀ (b : ZMod f) := by
  set χ := changeLevel h η₀
  have e1 : χ (b : ZMod m) = η₀ (b : ZMod f) := changeLevel_nat h η₀ b hb
  have e2 : χ (b : ZMod m) = χ.primitiveCharacter (b : ZMod χ.conductor) := by
    conv_lhs => rw [← changeLevel_primitiveCharacter χ]
    exact changeLevel_nat _ _ b hb
  rw [← e2, e1]
theorem three_ne_pm_one {P : ℕ} (hP : 7 ≤ P) :
    ((3 : ℕ) : ZMod P) ≠ 1 ∧ ((3 : ℕ) : ZMod P) ≠ -1 := by
  constructor
  · intro h
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega
  · intro h
    have h4 : ((4 : ℕ) : ZMod P) = 0 := by
      rw [show (4 : ℕ) = 3 + 1 by rfl, Nat.cast_add, h, Nat.cast_one]; ring
    rw [ZMod.natCast_eq_zero_iff] at h4
    exact absurd (Nat.le_of_dvd (by norm_num) h4) (by omega)
theorem exists_good_psi (hp7 : 7 ≤ p) (hr : 1 ≤ r) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hq : q = 2 ∨ q = 3) (E : Finset ℕ) (hE : E ⊆ {q}) (c : ℕ → ℂ) :
    ∃ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive ∧ ψ (-1) = ε ∧
      ∏ ℓ ∈ E, (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * c ℓ) ≠ 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hP7 : 7 ≤ p ^ r := le_trans hp7 (Nat.le_self_pow (by omega) p)
  by_contra H
  push Not at H
  have hcq : q.Coprime (p ^ r) := Nat.Coprime.pow_right r
    ((Nat.coprime_primes (by rcases hq with rfl | rfl <;> norm_num) hp.out).2 (by omega))
  set gq : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime q hcq
  have hgq : (gq : ZMod (p ^ r)) = ((q : ℕ) : ZMod (p ^ r)) := ZMod.coe_unitOfCoprime q hcq
  have hpm1 : ((q : ℕ) : ZMod (p ^ r)) ≠ 1 ∧ ((q : ℕ) : ZMod (p ^ r)) ≠ -1 := by
    rcases hq with rfl | rfl
    · exact two_ne_pm_one hP7
    · exact three_ne_pm_one hP7
  rcases subset_singleton_iff.1 hE with h0 | h1
  · have := Erdos634.LemmaSG2.lemmaG hp7 hr hε gq 0 (fun ψ hψ hψε => by
      have := H ψ hψ hψε; rw [h0, prod_empty] at this; exact absurd this one_ne_zero)
    rw [hgq] at this
    rcases this with h | h
    · exact hpm1.1 h
    · exact hpm1.2 h
  · have := Erdos634.LemmaSG2.lemmaG hp7 hr hε gq (c q) (fun ψ hψ hψε => by
      have h := H ψ hψ hψε
      rw [h1, prod_singleton] at h
      have hψq : ψ (gq : ZMod (p ^ r)) ≠ 0 := Erdos634.DirichletCRT.unit_val_ne_zero _ _
      rw [hgq] at hψq ⊢
      rw [MulChar.inv_apply_eq_inv'] at h
      have h' : (ψ ((q : ℕ) : ZMod (p ^ r)))⁻¹ * c q = 1 := by linear_combination -h
      calc ψ ((q : ℕ) : ZMod (p ^ r))
          = ψ ((q : ℕ) : ZMod (p ^ r)) * ((ψ ((q : ℕ) : ZMod (p ^ r)))⁻¹ * c q) := by rw [h', mul_one]
        _ = c q := by rw [← mul_assoc, mul_inv_cancel₀ hψq, one_mul])
    rw [hgq] at this
    rcases this with h | h
    · exact hpm1.1 h
    · exact hpm1.2 h
theorem key_level2 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hβ : (y : ZMod (p ^ r)) = (σ : ZMod (p ^ r)) * x)
    {f : ℕ} [NeZero f] (hfm : f ∣ m) {q : ℕ} (hq : q = 2 ∨ q = 3) (hE : eulerPrimes m f ⊆ {q})
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → ¬ p ∣ w → classSum a e w ≠ 0 → ¬ f ∣ dm m w) :
    ∀ η₀ : DirichletCharacter ℂ f, η₀.IsPrimitive →
      ((classSum a e x : ℚ) : ℂ) * η₀ (x : ZMod f) +
        (σ : ℂ) * (classSum a e y : ℚ) * η₀ (((σ * y : ℤ)) : ZMod f) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro η₀ hη₀
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  set ε : ℂ := -η (-1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases η.even_or_odd with h | h
    · right; simp only [ε, show η (-1) = 1 from h]
    · left; simp only [ε, show η (-1) = -1 from h, neg_neg]
  have hη2 : η (-1) * η (-1) = 1 := by
    rcases η.even_or_odd with h | h
    · rw [show η (-1) = 1 from h]; ring
    · rw [show η (-1) = -1 from h]; ring
  have hE' : eulerPrimes m η.conductor ⊆ {q} := by rw [hηc]; exact hE
  obtain ⟨ψ, hψ, hψε, hEul⟩ := exists_good_psi hp7 hr hε hq (eulerPrimes m η.conductor) hE'
    (fun ℓ => η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
  have hodd : (chi ψ η).Odd := by
    show (chi ψ η) (-1) = -1
    rw [MulChar.coeToFun_mul, Pi.mul_apply,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψε]
    simp only [ε]; linear_combination -hη2
  have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
  rw [regroup, sum_coe_sort (univ.image a)
    (fun w => ((classSum a e w : ℚ) : ℂ) * bracket (chi ψ η) w)] at hsum
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  rw [sum_eq_add_of_mem x y hxf.1 hyf.1 hxy] at hsum
  swap
  · intro w hw ⟨hwx, hwy⟩
    by_cases hpw : p ∣ w
    · rw [bracket_p_dvd hr hpm hψ η w hpw, mul_zero]
    by_cases hEw : classSum a e w = 0
    · rw [hEw]; simp
    rw [bracket_unit hpm hψ η w hpw, if_neg (by rw [hηc]; exact hdie w hw hwx hwy hpw hEw), mul_zero]
  have hterm : ∀ t : ℕ, t ∈ fullPts p m a →
      bracket (chi ψ η) t = ψ (t : ZMod (p ^ r)) * η₀ (t : ZMod f) *
        ∏ ℓ ∈ eulerPrimes m η.conductor,
          (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor)) := by
    intro t ht
    have htf := mem_filter.1 ht
    have hdm : dm m t = m := (dm_eq_iff t).2 htf.2.2
    have hg : m.gcd t = 1 := Nat.coprime_comm.1 htf.2.2
    rw [bracket_unit hpm hψ η t htf.2.1, if_pos (by rw [hηc, hdm]; exact hfm), hg, Nat.div_one, hdm,
      primChar_lift hfm η₀ t htf.2.2,
      div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne'),
      one_mul]
  rw [hterm x hx, hterm y hy] at hsum
  set Eul := ∏ ℓ ∈ eulerPrimes m η.conductor,
    (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
  have hψx : ψ (x : ZMod (p ^ r)) ≠ 0 := by
    have hxP : x.Coprime (p ^ r) :=
      Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
    rw [← ZMod.coe_unitOfCoprime x hxP]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hψy : ψ (y : ZMod (p ^ r)) = ψ (σ : ZMod (p ^ r)) * ψ (x : ZMod (p ^ r)) := by
    rw [hβ, map_mul]
  rw [hψy] at hsum
  have hfac : ψ (x : ZMod (p ^ r)) * Eul *
      (((classSum a e x : ℚ) : ℂ) * η₀ (x : ZMod f) +
        ψ (σ : ZMod (p ^ r)) * ((classSum a e y : ℚ) : ℂ) * η₀ (y : ZMod f)) = 0 := by
    linear_combination hsum
  have hrel := (mul_eq_zero.1 hfac).resolve_left (mul_ne_zero hψx hEul)
  rcases hσ with rfl | rfl
  · rw [show (((1 * y : ℤ)) : ZMod f) = (y : ZMod f) by push_cast; ring]
    simp only [Int.cast_one, map_one] at hrel
    push_cast; linear_combination hrel
  · have hm1 : η₀ (((-1 * y : ℤ)) : ZMod f) = η₀ (-1) * η₀ (y : ZMod f) := by
      rw [← map_mul]; congr 1; push_cast; ring
    have hψm : ψ ((-1 : ℤ) : ZMod (p ^ r)) = -η₀ (-1) := by
      rw [Int.cast_neg, Int.cast_one, hψε]
      simp only [ε, η, Erdos634.LemmaSG2.changeLevel_neg_one]
    rw [hψm] at hrel
    rw [hm1]; push_cast; linear_combination hrel
theorem tau_drop {q v v' m' : ℕ} (hq : q.Prime) (hv : 1 ≤ v) (hm' : m' ≠ 0) (hqm' : ¬ q ∣ m')
    {z : ℤ} (hSp : Sp (q ^ v * m') z) (hne : ¬ z ≡ 1 [ZMOD (q : ℤ) ^ v])
    (hv' : v' = 0 ∨ (q = 2 ∧ v' = v - 1 ∧ 3 ≤ v)) :
    Sp (q ^ v' * m') z ∧ tau (q ^ v' * m') z + 1 = tau (q ^ v * m') z := by
  have hc : ∀ k, (q ^ k).Coprime m' := fun k =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 hqm')
  have hq0 : ∀ k, q ^ k ≠ 0 := fun k => pow_ne_zero _ hq.ne_zero
  obtain ⟨hSq, hSm'⟩ := (Sp_mul (hc v) (hq0 v) hm' z).1 hSp
  rw [Sp_pp hq (by omega)] at hSq
  have htv : tau (q ^ v * m') z = 1 + tau m' z := by
    rw [tau_mul (hc v) (hq0 v) hm', tau_pp hq (by omega), if_neg hne]
  rcases hv' with rfl | ⟨rfl, rfl, hv3⟩
  · rw [pow_zero, one_mul, htv]; exact ⟨hSm', by ring⟩
  · have hz1 : z ≡ 1 [ZMOD ((2 : ℕ) : ℤ) ^ (v - 1)] := by
      rcases hSq with h | ⟨h, -⟩ | ⟨-, -, h⟩
      · exact absurd h hne
      · exact absurd h (by norm_num)
      · have hp' : (2 : ℤ) ^ v = 2 ^ (v - 1) * 2 := by rw [← pow_succ]; congr 1; omega
        have h' := h.of_dvd (show (2 : ℤ) ^ (v - 1) ∣ 2 ^ v from ⟨2, hp'⟩)
        push_cast
        refine h'.trans ?_
        rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
    refine ⟨(Sp_mul (hc _) (hq0 _) hm' z).2 ⟨(Sp_pp hq (by omega) z).2 (Or.inl hz1), hSm'⟩, ?_⟩
    rw [tau_mul (hc _) (hq0 _) hm', tau_pp hq (by omega), if_pos hz1, htv]; ring
theorem euler_sub {q v v' m' : ℕ} (hq : q.Prime) {ℓ : ℕ}
    (hl : ℓ ∈ eulerPrimes (q ^ v * m') (q ^ v' * m')) : ℓ = q := by
  simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors] at hl
  obtain ⟨⟨hl, hld, -⟩, hn⟩ := hl
  rcases hl.dvd_mul.1 hld with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hl hq).1 (hl.dvd_of_dvd_pow h)
  · exact absurd (dvd_mul_of_dvd_right h _) hn
theorem f2_mod4 {q v v' m' : ℕ} (hq : q = 2 ∨ q = 3) (hqm' : ¬ q ∣ m')
    (hm4 : (q ^ v * m') % 4 ≠ 2) (hv' : v' = 0 ∨ (q = 2 ∧ v' = v - 1 ∧ 3 ≤ v)) :
    (q ^ v' * m') % 4 ≠ 2 := by
  rcases hv' with rfl | ⟨rfl, rfl, hv3⟩
  · rw [pow_zero, one_mul]
    rcases hq with rfl | rfl
    · omega
    · intro h
      apply hm4
      have ho : 3 ^ v % 4 = 1 ∨ 3 ^ v % 4 = 3 := by
        have : 3 ^ v % 2 = 1 := Nat.pow_mod 3 v 2 ▸ by simp
        omega
      rw [Nat.mul_mod, h]
      rcases ho with e | e <;> rw [e]
  · have : 4 ∣ 2 ^ (v - 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
    have := dvd_mul_of_dvd_left this m'
    omega
theorem lemmaL (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m)
    {q v v' m' : ℕ} (hq : q = 2 ∨ q = 3) (hv : 1 ≤ v) (hqm' : ¬ q ∣ m') (hm : m = q ^ v * m')
    (hm4 : m % 4 ≠ 2) (hv' : v' = 0 ∨ (q = 2 ∧ v' = v - 1 ∧ 3 ≤ v))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hβ : (y : ZMod (p ^ r)) = (σ : ZMod (p ^ r)) * x)
    (hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card)
    (z : ℤ) (hz : z * (σ * y) ≡ x [ZMOD m]) (hne : ¬ z ≡ 1 [ZMOD (q : ℤ) ^ v])
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → ¬ p ∣ w → classSum a e w ≠ 0 →
      ¬ (q ^ v' * m') ∣ dm m w) :
    classSum a e x = 0 ∧ classSum a e y = 0 := by
  have hqp : q.Prime := by rcases hq with rfl | rfl <;> norm_num
  have hm'0 : m' ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact NeZero.ne m hm
  haveI : NeZero m' := ⟨hm'0⟩
  set f := q ^ v' * m' with hf
  haveI : NeZero f := ⟨Nat.mul_ne_zero (pow_ne_zero _ hqp.ne_zero) hm'0⟩
  have hfm : f ∣ m := by
    rw [hm]; refine Nat.mul_dvd_mul_right (Nat.pow_dvd_pow q ?_) m'
    rcases hv' with rfl | ⟨-, rfl, -⟩ <;> omega
  have hf4 : f % 4 ≠ 2 := f2_mod4 hq hqm' (hm ▸ hm4) hv'
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hmS := rel_Gprime hm4 _ _ x y hxf.2.2 hyf.2.2 σ hσ z hz
    (fc_key hp7 hr hpm a e hP x y hx hy hxy σ hσ hβ hsep hN)
  rcases hmS with h | ⟨hSp, hrel1⟩
  · exact h
  have hE : eulerPrimes m f ⊆ {q} := fun ℓ hl => mem_singleton.2 (euler_sub hqp (hm ▸ hl))
  have hzf : z * (σ * y) ≡ x [ZMOD f] := hz.of_dvd (by exact_mod_cast hfm)
  have hfS := rel_Gprime hf4 _ _ x y (hxf.2.2.coprime_dvd_right hfm) (hyf.2.2.coprime_dvd_right hfm)
    σ hσ z hzf (key_level2 hp7 hr hpm a e hP x y hx hy hxy σ hσ hβ hfm hq hE hdie)
  obtain ⟨-, htau⟩ := tau_drop hqp hv hm'0 hqm' (hm ▸ hSp) hne hv'
  rw [← hm] at htau
  rcases hfS with h | ⟨-, hrel2⟩
  · exact h
  have hσ2 : (σ : ℚ) * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hx0 : classSum a e x = 0 := by
    have h := hrel1.symm.trans hrel2
    rw [← htau, pow_succ] at h
    have : 2 * ((-1 : ℚ) ^ tau f z * σ) * classSum a e x = 0 := by linear_combination h
    have hne0 : (-1 : ℚ) ^ tau f z * σ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (by rcases hσ with rfl | rfl <;> norm_num)
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hne0)
  exact ⟨hx0, by rw [hrel1, hx0, mul_zero]⟩
end L
end Erdos634.LemmaSL
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSR3
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit sum_indicator)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSFC (fullPts dm_eq_iff card_val_le_one card_N)
open Erdos634.LemmaSN (pred_dvd lemmaN_a lemmaN_b)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive primChar_ne_zero)
noncomputable def Phi2 {P : ℕ} (A B c : ℂ) (X Q T : ZMod P) (u : (ZMod P)ˣ) : ℂ :=
  A * (if (u : ZMod P) = X then 1 else 0) - A * c * (if (u : ZMod P) * Q = X then 1 else 0) +
    B * (if (u : ZMod P) = T then 1 else 0)
theorem psi_Phi2 {P : ℕ} [NeZero P] (ψ : DirichletCharacter ℂ P) (A B c : ℂ) (X Q T : ZMod P)
    (hQ : IsUnit Q) :
    ∑ u : (ZMod P)ˣ, ψ (u : ZMod P) * Phi2 A B c X Q T u =
      A * ψ X - A * c * (ψ X * (ψ Q)⁻¹) + B * ψ T := by
  have h1 := sum_indicator ψ 1 X isUnit_one
  have hQ' := sum_indicator ψ Q X hQ
  have hT := sum_indicator ψ 1 T isUnit_one
  simp only [mul_one, map_one, inv_one] at h1 hT
  unfold Phi2
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  rw [← hQ', ← h1, ← hT, mul_sum, mul_sum, mul_sum]
  congr 1; congr 1
  all_goals refine sum_congr rfl (fun u _ => by ring)
section L2
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem level2_three (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    {f : ℕ} [NeZero f] (hfm : f ∣ m) (hf4 : f % 4 ≠ 2) (hf34 : f ≠ 3 ∧ f ≠ 4)
    {q : ℕ} (hq : q = 2 ∨ q = 3) (hE : eulerPrimes m f ⊆ {q})
    (x y t : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x) (hxyf : x ≡ y [MOD f])
    (ht : t ∈ univ.image a) (hpt : ¬ p ∣ t) (hdt : dm m t = f) (htx : t ≠ x) (hty : t ≠ y)
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → w ≠ t → ¬ p ∣ w → classSum a e w ≠ 0 →
      ¬ f ∣ dm m w)
    (hsep : let X := (x : ZMod (p ^ r)); let Q := (q : ZMod (p ^ r));
      let T := ((t / m.gcd t : ℕ) : ZMod (p ^ r));
      X * Q ≠ X ∧ X ≠ T ∧ -X ≠ X ∧ -X * Q ≠ X ∧ -X ≠ T ∧ T * Q ≠ X ∧ -T ≠ T) :
    classSum a e t = 0 ∧ classSum a e x + classSum a e y = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hsep
  set X : ZMod (p ^ r) := (x : ZMod (p ^ r))
  set Q : ZMod (p ^ r) := (q : ZMod (p ^ r))
  set bt := t / m.gcd t
  set T : ZMod (p ^ r) := (bt : ZMod (p ^ r))
  obtain ⟨η₀, hη₀, hev⟩ := (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne f) hf4).2 hf34
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  have hηev : η (-1) = 1 := by
    simp only [η, Erdos634.LemmaSG2.changeLevel_neg_one]; exact hev
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hqP : q.Coprime (p ^ r) := Nat.Coprime.pow_right r
    ((Nat.coprime_primes (by rcases hq with rfl | rfl <;> norm_num) hp.out).2 (by omega))
  have hQu : IsUnit Q := (ZMod.isUnit_iff_coprime q _).2 hqP
  set c' : ℂ := if q ∈ eulerPrimes m η.conductor then
    η.primitiveCharacter⁻¹ (q : ZMod η.conductor) else 0
  have hEul : ∀ ψ : DirichletCharacter ℂ (p ^ r),
      ∏ ℓ ∈ eulerPrimes m η.conductor,
        (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
        = 1 - ψ⁻¹ (q : ZMod (p ^ r)) * c' := by
    intro ψ
    have hE' : eulerPrimes m η.conductor ⊆ {q} := by rw [hηc]; exact hE
    rcases subset_singleton_iff.1 hE' with h0 | h1
    · rw [h0, prod_empty]; simp [c', h0]
    · rw [h1, prod_singleton]; simp [c', h1]
  set wt : ℂ := (m.totient : ℂ) / (f.totient : ℂ)
  set A : ℂ := ((classSum a e x : ℚ) : ℂ) * η.primitiveCharacter (x : ZMod η.conductor) +
    ((classSum a e y : ℚ) : ℂ) * η.primitiveCharacter (y : ZMod η.conductor)
  set B : ℂ := ((classSum a e t : ℚ) : ℂ) * wt * η.primitiveCharacter (bt : ZMod η.conductor)
  have hcomp : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Phi2 A B c' X Q T u = 0 := by
    intro ψ hψ hψo
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψo, hηev, mul_one]
    have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [regroup, sum_coe_sort (univ.image a)
      (fun w => ((classSum a e w : ℚ) : ℂ) * bracket (chi ψ η) w)] at hsum
    have hsub : ({x, y, t} : Finset ℕ) ⊆ univ.image a := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxf.1
      · exact hyf.1
      · exact ht
    rw [← sum_subset hsub (fun w hw hw' => by
      simp only [mem_insert, mem_singleton, not_or] at hw'
      obtain ⟨hwx, hwy, hwt⟩ := hw'
      by_cases hpw : p ∣ w
      · rw [bracket_p_dvd hr hpm hψ η w hpw, mul_zero]
      by_cases hEw : classSum a e w = 0
      · rw [hEw]; simp
      rw [bracket_unit hpm hψ η w hpw,
        if_neg (by rw [hηc]; exact hdie w hw hwx hwy hwt hpw hEw), mul_zero])] at hsum
    rw [sum_insert (by simp [hxy, htx.symm]), sum_insert (by simp [hty.symm]), sum_singleton]
      at hsum
    have hterm : ∀ s : ℕ, s ∈ fullPts p m a →
        bracket (chi ψ η) s = ψ (s : ZMod (p ^ r)) * η.primitiveCharacter (s : ZMod η.conductor) *
          (1 - ψ⁻¹ (q : ZMod (p ^ r)) * c') := by
      intro s hs
      have hsf := mem_filter.1 hs
      have hdm : dm m s = m := (dm_eq_iff s).2 hsf.2.2
      have hg : m.gcd s = 1 := Nat.coprime_comm.1 hsf.2.2
      rw [bracket_unit hpm hψ η s hsf.2.1, if_pos (by rw [hηc, hdm]; exact hfm), hg, Nat.div_one,
        hdm, hEul ψ,
        div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne'),
        one_mul]
    have htt : bracket (chi ψ η) t = wt * ψ T * η.primitiveCharacter (bt : ZMod η.conductor) := by
      rw [bracket_unit hpm hψ η t hpt, if_pos (by rw [hηc, hdt]), hdt]
      have hE0 : eulerPrimes f η.conductor = ∅ := by
        rw [hηc]; ext ℓ
        simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
        rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
      rw [hE0, prod_empty, mul_one]
    rw [hterm x hx, hterm y hy, htt, hβ] at hsum
    rw [psi_Phi2 ψ A B c' X Q T hQu, MulChar.inv_apply_eq_inv' ψ] at *
    simp only [A, B]
    linear_combination hsum
  have hsym : ∀ u, Phi2 A B c' X Q T u = Phi2 A B c' X Q T (-u) := by
    rcases Nat.lt_or_ge r 2 with h1 | h2
    · obtain rfl : r = 1 := by omega
      exact lemmaN_b _ hcomp
    · intro u
      have := lemmaN_a hr (Phi2 A B c' X Q T) (Or.inr rfl) hcomp (fun u => ?_) u
      · rw [this]; ring
      rw [card_N hr, if_neg (by omega)]
      obtain ⟨Qu, hQu'⟩ := id hQu
      set Y : ZMod (p ^ r) := X * ((Qu⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))
      have hY : ∀ w : ZMod (p ^ r), w * Q = X → w = Y := by
        intro w hw
        simp only [Y, ← hw, ← hQu', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      set S6 : Finset (ZMod (p ^ r)) := {X, Y, T, -X, -Y, -T}
      have h6 : S6.card ≤ 6 := by
        refine (card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
        simp
      refine lt_of_le_of_lt ?_ (show 6 < p by omega)
      refine le_trans (card_le_card_of_injOn (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)))
        (t := S6) (fun v hv => ?_) (fun v _ w _ h => Units.ext h)) h6
      have hv' := (mem_filter.1 hv).2.2
      simp only [S6, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      unfold Phi2 at hv'
      rcases hv' with h | h
      · by_contra hc; push Not at hc; apply h
        rw [if_neg hc.1, if_neg (fun h' => hc.2.1 (hY _ h')), if_neg hc.2.2.1]; ring
      · by_contra hc; push Not at hc; apply h
        simp only [Units.val_neg]
        rw [if_neg (fun h' => hc.2.2.2.1 (by rw [← h', neg_neg])),
          if_neg (fun h' => hc.2.2.2.2.1 (by rw [← hY _ h', neg_neg])),
          if_neg (fun h' => hc.2.2.2.2.2 (by rw [← h', neg_neg]))]; ring
  have hxP : x.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  have hbtP : bt.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      (fun h => hpt (dvd_trans h (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m t))))).symm
  set uX : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime x hxP
  set uT : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime bt hbtP
  have huX : (uX : ZMod (p ^ r)) = X := ZMod.coe_unitOfCoprime x hxP
  have huT : (uT : ZMod (p ^ r)) = T := ZMod.coe_unitOfCoprime bt hbtP
  have hA : A = 0 := by
    have h := hsym uX
    unfold Phi2 at h
    simp only [Units.val_neg, huX] at h
    rw [if_pos trivial, if_neg hs1, if_neg hs2, if_neg hs3, if_neg hs4, if_neg hs5] at h
    linear_combination h
  have hB : B = 0 := by
    have h := hsym uT
    unfold Phi2 at h
    simp only [Units.val_neg, huT, hA, zero_mul, zero_sub, mul_zero, neg_zero, zero_add] at h
    rw [if_pos trivial, if_neg hs7] at h
    linear_combination h
  have hgpos : 0 < m.gcd t := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have hbtf : bt.Coprime η.conductor := by
    rw [hηc, ← hdt]; exact (Nat.coprime_div_gcd_div_gcd hgpos).symm
  have hwt : wt ≠ 0 := div_ne_zero
    (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
    (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne f))).ne')
  have hEt : classSum a e t = 0 := by
    have := (mul_eq_zero.1 hB).resolve_right (primChar_ne_zero η bt hbtf)
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hwt
  have hxc : x.Coprime η.conductor := by rw [hηc]; exact hxf.2.2.coprime_dvd_right hfm
  have hxy' : (x : ZMod η.conductor) = (y : ZMod η.conductor) := by
    rw [ZMod.natCast_eq_natCast_iff, hηc]; exact hxyf
  simp only [A, ← hxy'] at hA
  have : ((classSum a e x + classSum a e y : ℚ) : ℂ) *
      η.primitiveCharacter (x : ZMod η.conductor) = 0 := by push_cast; linear_combination hA
  exact ⟨hEt, by exact_mod_cast (mul_eq_zero.1 this).resolve_right (primChar_ne_zero η x hxc)⟩
theorem tau_eq_zero {d : ℕ} {z : ℤ} (hz : z ≡ 1 [ZMOD d]) : Erdos634.LemmaSGprime.tau d z = 0 := by
  classical
  unfold Erdos634.LemmaSGprime.tau
  rw [card_eq_zero, filter_eq_empty_iff]
  intro q _ h
  apply h
  exact hz.of_dvd (by exact_mod_cast Nat.ordProj_dvd d q)
theorem kX_ne {P : ℕ} [Fact (1 < P)] {X : ZMod P} (hX : IsUnit X) (k : ℕ) (hk : k.Coprime P) :
    (k : ZMod P) * X ≠ 0 :=
  (((ZMod.isUnit_iff_coprime k P).2 hk).mul hX).ne_zero
theorem top_equal (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    {q v m' : ℕ} (hq : q.Prime) (hv : 1 ≤ v) (hm : m = q ^ v * m') (hqm' : ¬ q ∣ m')
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x)
    (hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card)
    (hxym' : x ≡ y [MOD m']) (hxyq : ¬ x ≡ y [MOD q ^ v]) :
    classSum a e y = classSum a e x := by
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hm'0 : m' ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact NeZero.ne m hm
  haveI : NeZero m' := ⟨hm'0⟩
  set z : ℤ := (((x : ZMod m) * (y : ZMod m)⁻¹).val : ℤ)
  have hzm : ((z : ℤ) : ZMod m) * (y : ZMod m) = x := by
    simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val, mul_assoc]
    rw [mul_comm ((y : ZMod m))⁻¹, ZMod.coe_mul_inv_eq_one y hyf.2.2, mul_one]
  have hz : z * (1 * y) ≡ x [ZMOD m] := by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [one_mul]; exact hzm
  have hkey := Erdos634.LemmaSL.fc_key hp7 hr hpm a e hP x y hx hy hxy 1 (Or.inl rfl) (by rw [hβ]; push_cast; ring)
    hsep hN
  rcases Erdos634.LemmaSL.rel_Gprime hm4 _ _ x y hxf.2.2 hyf.2.2 1 (Or.inl rfl) z hz hkey with
    ⟨h1, h2⟩ | ⟨-, hrel⟩
  · rw [h1, h2]
  have hcop : (q ^ v).Coprime m' := Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hq).2 hqm')
  have hzq : ¬ z ≡ 1 [ZMOD (q : ℤ) ^ v] := by
    intro h
    apply hxyq
    have h1 : ((z : ℤ) : ZMod (q ^ v)) = 1 := by
      rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff]; push_cast; exact h
    have h2 : ((z : ℤ) : ZMod (q ^ v)) * (y : ZMod (q ^ v)) = x := by
      have := congrArg (ZMod.castHom (show q ^ v ∣ m by rw [hm]; exact Nat.dvd_mul_right _ _)
        (ZMod (q ^ v))) hzm
      rwa [map_mul, map_intCast, map_natCast, map_natCast] at this
    rw [h1, one_mul] at h2
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).1 h2).symm
  have hzm' : z ≡ 1 [ZMOD m'] := by
    have h2 : ((z : ℤ) : ZMod m') * (y : ZMod m') = x := by
      have := congrArg (ZMod.castHom (show m' ∣ m by rw [hm]; exact Nat.dvd_mul_left _ _)
        (ZMod m')) hzm
      rwa [map_mul, map_intCast, map_natCast, map_natCast] at this
    have hxy' : (x : ZMod m') = y := (ZMod.natCast_eq_natCast_iff _ _ _).2 hxym'
    rw [hxy'] at h2
    have hyu : IsUnit (y : ZMod m') :=
      (ZMod.isUnit_iff_coprime y m').2 (hyf.2.2.coprime_dvd_right (by rw [hm]; exact Nat.dvd_mul_left _ _))
    have : ((z : ℤ) : ZMod m') = 1 := by
      obtain ⟨u, hu⟩ := hyu
      rw [← hu] at h2
      have := congrArg (· * ((u⁻¹ : (ZMod m')ˣ) : ZMod m')) h2
      simpa [mul_assoc] using this
    rw [← ZMod.intCast_eq_intCast_iff, this, Int.cast_one]
  have htau : Erdos634.LemmaSGprime.tau m z = 1 := by
    rw [hm, Erdos634.LemmaSGprime.tau_mul hcop (pow_ne_zero _ hq.ne_zero) hm'0,
      Erdos634.LemmaSGprime.tau_pp hq (by omega), if_neg hzq, tau_eq_zero hzm']
  rw [hrel, htau]; push_cast; ring
theorem setup3 (hp7 : 7 ≤ p) (hr : 1 ≤ r) {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (e : ι → ℚ) (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y)
    (hxm : x.Coprime m) (hym : y.Coprime m) (htm : ¬ t.Coprime m) (hβ : (y : ZMod (p ^ r)) = x) :
    x ∈ fullPts p m a ∧ y ∈ fullPts p m a ∧
    (∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x) ∧
    (2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) ∧
    (∀ w ∈ univ.image a, w ≠ x → w ≠ y → w ≠ t → False) := by
  have hmem : ∀ w, w ∈ univ.image a ↔ w = x ∨ w = y ∨ w = t := by
    intro w; rw [himg]; simp
  have hsub : ∀ w ∈ fullPts p m a, w = x ∨ w = y := by
    intro w hw
    have hwf := mem_filter.1 hw
    rcases (hmem w).1 hwf.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h; exact absurd hwf.2.2 htm
  refine ⟨mem_filter.2 ⟨(hmem x).2 (Or.inl rfl), hpx, hxm⟩,
    mem_filter.2 ⟨(hmem y).2 (Or.inr (Or.inl rfl)), hpy, hym⟩, ?_, ?_, ?_⟩
  · intro w hw hwx hwy
    rcases hsub w hw with h | h <;> contradiction
  · have hc : ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card ≤ 1 := by
      refine card_le_one.2 (fun u hu v hv => ?_)
      obtain ⟨w1, hw1, rfl⟩ := mem_image.1 hu
      obtain ⟨w2, hw2, rfl⟩ := mem_image.1 hv
      rcases hsub w1 hw1 with rfl | rfl <;> rcases hsub w2 hw2 with rfl | rfl <;>
        simp [hβ]
    rw [card_N hr]
    split_ifs <;> omega
  · intro w hw hwx hwy hwt
    rcases (hmem w).1 hw with h | h | h <;> contradiction
theorem small_cop {k : ℕ} (hk : 0 < k) (hk7 : k < 7) (hp7 : 7 ≤ p) : k.Coprime (p ^ r) :=
  Nat.Coprime.pow_right r (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
    (fun h => by have := Nat.le_of_dvd hk h; omega)))
theorem lemmaR3 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {m' : ℕ} (hm : m = 3 * m')
    (h3 : ¬ 3 ∣ m') (hmodd : m % 2 = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : ¬ p ∣ t) (hxm : x.Coprime m) (hym : y.Coprime m)
    (hgt : m.gcd t = 3) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x)
    (hxym' : x ≡ y [MOD m']) (hxy3 : ¬ x ≡ y [MOD 3]) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e t = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  have hm'0 : m' ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact NeZero.ne m hm
  haveI : NeZero m' := ⟨hm'0⟩
  have hm'odd : m' % 2 = 1 := by omega
  have htm : ¬ t.Coprime m := fun h => by rw [Nat.coprime_comm] at h; rw [h] at hgt; omega
  obtain ⟨hx, hy, hsep, hN, hdie⟩ := setup3 hp7 hr a e x y t himg hpx hpy hxm hym htm hβ
  have hEq := top_equal hp7 hr hpm (by omega) (q := 3) (v := 1) (m' := m') Nat.prime_three le_rfl
    (by rw [hm, pow_one]) h3 a e hP x y hx hy hxy hβ hsep hN hxym' (by rwa [pow_one])
  have hdt : dm m t = m' := by
    rw [dm, hgt, hm, Nat.mul_div_cancel_left _ (by norm_num)]
  have htx : t ≠ x := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hxm)] at hgt; omega
  have hty : t ≠ y := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hym)] at hgt; omega
  have hE : eulerPrimes m m' ⊆ {3} := fun ℓ hl => mem_singleton.2
    (Erdos634.LemmaSL.euler_sub (v := 1) (v' := 0) Nat.prime_three
      (by rwa [pow_one, pow_zero, one_mul, ← hm]))
  have hX : IsUnit ((x : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime x _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpx).symm)
  have hT : (3 : ZMod (p ^ r)) * ((t / m.gcd t : ℕ) : ZMod (p ^ r)) + 2 * (x : ZMod (p ^ r)) = 0 := by
    have h3t : t / m.gcd t * 3 = t := by rw [hgt]; exact Nat.div_mul_cancel (hgt ▸ Nat.gcd_dvd_right m t)
    have hs : ((x + y + t : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [← h3t] at hs; push_cast at hs; rw [hβ] at hs
    linear_combination hs
  obtain ⟨hEt, hExy⟩ := level2_three hp7 hr hpm a e hP (f := m') (by rw [hm]; exact Nat.dvd_mul_left _ _)
    (by omega) ⟨fun h => h3 (by rw [h]), by omega⟩ (Or.inr rfl) hE x y t hx hy hxy hβ hxym'
    ((by rw [himg]; simp)) hpt hdt htx hty (fun w hw h1 h2 h4 _ _ _ => (hdie w hw h1 h2 h4).elim)
    (by
      intro X Q T
      have c1 := kX_ne hX 1 (small_cop (by norm_num) (by norm_num) hp7)
      have c2 := kX_ne hX 2 (small_cop (by norm_num) (by norm_num) hp7)
      have c3 := kX_ne hX 3 (small_cop (by norm_num) (by norm_num) hp7)
      have c4 := kX_ne hX 4 (small_cop (by norm_num) (by norm_num) hp7)
      have c5 := kX_ne hX 5 (small_cop (by norm_num) (by norm_num) hp7)
      push_cast at c1 c2 c3 c4 c5
      refine ⟨fun h => c2 (by linear_combination h), fun h => c5 (by linear_combination 3 * h + hT),
        fun h => c2 (by linear_combination -h), fun h => c4 (by linear_combination -h),
        fun h => c1 (by linear_combination -hT - 3 * h), fun h => c3 (by linear_combination hT - h),
        fun h => c4 (by linear_combination 2 * hT + 3 * h)⟩)
  have hx0 : classSum a e x = 0 := by linarith
  exact ⟨hx0, by linarith, hEt⟩
theorem lemmaR2b (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {m' : ℕ} (hm : m = 4 * m')
    (hm'odd : m' % 2 = 1) (hm'3 : m' ≠ 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : ¬ p ∣ t) (hxm : x.Coprime m) (hym : y.Coprime m)
    (hgt : m.gcd t = 4) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x)
    (hxym' : x ≡ y [MOD m']) (hxy4 : ¬ x ≡ y [MOD 4]) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e t = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  have hm'0 : m' ≠ 0 := by omega
  haveI : NeZero m' := ⟨hm'0⟩
  have htm : ¬ t.Coprime m := fun h => by rw [Nat.coprime_comm] at h; rw [h] at hgt; omega
  obtain ⟨hx, hy, hsep, hN, hdie⟩ := setup3 hp7 hr a e x y t himg hpx hpy hxm hym htm hβ
  have hEq := top_equal hp7 hr hpm (by omega) (q := 2) (v := 2) (m' := m') Nat.prime_two
    (by norm_num) (by rw [hm]; norm_num) (by omega) a e hP x y hx hy hxy hβ hsep hN hxym'
    (by norm_num; exact hxy4)
  have hdt : dm m t = m' := by
    rw [dm, hgt, hm, Nat.mul_div_cancel_left _ (by norm_num)]
  have htx : t ≠ x := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hxm)] at hgt; omega
  have hty : t ≠ y := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hym)] at hgt; omega
  have hE : eulerPrimes m m' ⊆ {2} := fun ℓ hl => mem_singleton.2
    (Erdos634.LemmaSL.euler_sub (v := 2) (v' := 0) Nat.prime_two
      (by rw [pow_zero, one_mul, show (2 : ℕ) ^ 2 * m' = m by rw [hm]; norm_num]; exact hl))
  have hX : IsUnit ((x : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime x _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpx).symm)
  have hT : (x : ZMod (p ^ r)) + 2 * ((t / m.gcd t : ℕ) : ZMod (p ^ r)) = 0 := by
    have h4t : t / m.gcd t * 4 = t := by rw [hgt]; exact Nat.div_mul_cancel (hgt ▸ Nat.gcd_dvd_right m t)
    have hs : ((x + y + t : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [← h4t] at hs; push_cast at hs; rw [hβ] at hs
    have h2 : IsUnit ((2 : ℕ) : ZMod (p ^ r)) :=
      (ZMod.isUnit_iff_coprime 2 _).2 (small_cop (by norm_num) (by norm_num) hp7)
    push_cast at h2
    exact (h2.mul_right_eq_zero).1 (by linear_combination hs)
  obtain ⟨hEt, hExy⟩ := level2_three hp7 hr hpm a e hP (f := m') (by rw [hm]; exact Nat.dvd_mul_left _ _)
    (by omega) ⟨hm'3, by omega⟩ (Or.inl rfl) hE x y t hx hy hxy hβ hxym'
    ((by rw [himg]; simp)) hpt hdt htx hty (fun w hw h1 h2 h4 _ _ _ => (hdie w hw h1 h2 h4).elim)
    (by
      intro X Q T
      have c1 := kX_ne hX 1 (small_cop (by norm_num) (by norm_num) hp7)
      have c2 := kX_ne hX 2 (small_cop (by norm_num) (by norm_num) hp7)
      have c3 := kX_ne hX 3 (small_cop (by norm_num) (by norm_num) hp7)
      push_cast at c1 c2 c3
      refine ⟨fun h => c1 (by linear_combination h), fun h => c3 (by linear_combination 2 * h + hT),
        fun h => c2 (by linear_combination -h), fun h => c3 (by linear_combination -h),
        fun h => c1 (by linear_combination -hT - 2 * h), fun h => c2 (by linear_combination hT - h),
        fun h => c1 (by linear_combination hT + h)⟩)
  have hx0 : classSum a e x = 0 := by linarith
  exact ⟨hx0, by linarith, hEt⟩
end L2
end Erdos634.LemmaSR3
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSR2a
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSFC (fullPts dm_eq_iff)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive primChar_ne_zero)
open Erdos634.LemmaSL (exists_good_psi primChar_lift euler_sub)
open Erdos634.LemmaSR3 (setup3 top_equal small_cop kX_ne tau_eq_zero)
open Erdos634.LemmaSGprime (Sp tau lemmaG' Sp_mul tau_mul Sp_pp tau_pp)
section R2a
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem level_eq (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    {f : ℕ} [NeZero f] (hfm : f ∣ m) (hE2 : eulerPrimes m f ⊆ {2})
    (x y t : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x)
    (ht : t ∈ univ.image a) (hpt : ¬ p ∣ t) (htx : t ≠ x) (hty : t ≠ y)
    (hfd : f ∣ dm m t) (hEul : eulerPrimes (dm m t) f = eulerPrimes m f)
    (hbt : (t / m.gcd t).Coprime m)
    (hTX : ((t / m.gcd t : ℕ) : ZMod (p ^ r)) = -(x : ZMod (p ^ r)))
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → w ≠ t → False) :
    ∀ η₀ : DirichletCharacter ℂ f, η₀.IsPrimitive →
      ((classSum a e x : ℚ) : ℂ) * η₀ (x : ZMod f) + ((classSum a e y : ℚ) : ℂ) * η₀ (y : ZMod f)
        - η₀ (-1) * ((m.totient : ℂ) / ((dm m t).totient : ℂ)) * ((classSum a e t : ℚ) : ℂ) *
          η₀ ((t / m.gcd t : ℕ) : ZMod f) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro η₀ hη₀
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  set ε : ℂ := -η (-1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases η.even_or_odd with h | h
    · right; simp only [ε, show η (-1) = 1 from h]
    · left; simp only [ε, show η (-1) = -1 from h, neg_neg]
  have hη2 : η (-1) * η (-1) = 1 := by
    rcases η.even_or_odd with h | h
    · rw [show η (-1) = 1 from h]; ring
    · rw [show η (-1) = -1 from h]; ring
  have hηm1 : η (-1) = η₀ (-1) := by simp only [η, Erdos634.LemmaSG2.changeLevel_neg_one]
  have hE' : eulerPrimes m η.conductor ⊆ {2} := by rw [hηc]; exact hE2
  obtain ⟨ψ, hψ, hψε, hEul0⟩ := exists_good_psi hp7 hr hε (Or.inl rfl) (eulerPrimes m η.conductor) hE'
    (fun ℓ => η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
  set Eul := ∏ ℓ ∈ eulerPrimes m η.conductor,
    (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
  have hodd : (chi ψ η).Odd := by
    show (chi ψ η) (-1) = -1
    rw [MulChar.coeToFun_mul, Pi.mul_apply,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψε]
    simp only [ε]; linear_combination -hη2
  have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
  rw [regroup, sum_coe_sort (univ.image a)
    (fun w => ((classSum a e w : ℚ) : ℂ) * bracket (chi ψ η) w)] at hsum
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hsub : ({x, y, t} : Finset ℕ) ⊆ univ.image a := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxf.1
    · exact hyf.1
    · exact ht
  rw [← sum_subset hsub (fun w hw hw' => by
    simp only [mem_insert, mem_singleton, not_or] at hw'
    exact (hdie w hw hw'.1 hw'.2.1 hw'.2.2).elim)] at hsum
  rw [sum_insert (by simp [hxy, htx.symm]), sum_insert (by simp [hty.symm]), sum_singleton] at hsum
  have hterm : ∀ s : ℕ, s ∈ fullPts p m a →
      bracket (chi ψ η) s = ψ (s : ZMod (p ^ r)) * η₀ (s : ZMod f) * Eul := by
    intro s hs
    have hsf := mem_filter.1 hs
    have hdm : dm m s = m := (dm_eq_iff s).2 hsf.2.2
    have hg : m.gcd s = 1 := Nat.coprime_comm.1 hsf.2.2
    rw [bracket_unit hpm hψ η s hsf.2.1, if_pos (by rw [hηc, hdm]; exact hfm), hg, Nat.div_one, hdm,
      primChar_lift hfm η₀ s hsf.2.2,
      div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne'),
      one_mul]
  have htt : bracket (chi ψ η) t = ((m.totient : ℂ) / ((dm m t).totient : ℂ)) *
      ψ ((t / m.gcd t : ℕ) : ZMod (p ^ r)) * η₀ ((t / m.gcd t : ℕ) : ZMod f) * Eul := by
    have hEul' : eulerPrimes (dm m t) η.conductor = eulerPrimes m η.conductor := by
      rw [hηc]; exact hEul
    rw [bracket_unit hpm hψ η t hpt, if_pos (by rw [hηc]; exact hfd), hEul',
      primChar_lift hfm η₀ _ hbt]
  rw [hterm x hx, hterm y hy, htt, hβ, hTX] at hsum
  have hψx : ψ (x : ZMod (p ^ r)) ≠ 0 := by
    have hxP : x.Coprime (p ^ r) :=
      Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
    rw [← ZMod.coe_unitOfCoprime x hxP]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hneg : ψ (-(x : ZMod (p ^ r))) = ε * ψ (x : ZMod (p ^ r)) := by
    rw [neg_eq_neg_one_mul, map_mul, hψε]
  rw [hneg] at hsum
  have hfac : ψ (x : ZMod (p ^ r)) * Eul *
      (((classSum a e x : ℚ) : ℂ) * η₀ (x : ZMod f) + ((classSum a e y : ℚ) : ℂ) * η₀ (y : ZMod f)
        - η₀ (-1) * ((m.totient : ℂ) / ((dm m t).totient : ℂ)) * ((classSum a e t : ℚ) : ℂ) *
          η₀ ((t / m.gcd t : ℕ) : ZMod f)) = 0 := by
    simp only [ε, hηm1] at hsum
    linear_combination hsum
  exact (mul_eq_zero.1 hfac).resolve_left (mul_ne_zero hψx hEul0)
theorem Sp_of_one {d : ℕ} {z : ℤ} (hz : z ≡ 1 [ZMOD d]) : Sp d z := by
  intro q _
  left
  exact hz.of_dvd (by exact_mod_cast Nat.ordProj_dvd d q)
theorem primeFactors_two_pow_mul {k m' : ℕ} (hk : 1 ≤ k) (hm' : m' ≠ 0) :
    (2 ^ k * m').primeFactors = {2} ∪ m'.primeFactors := by
  rw [Nat.primeFactors_mul (pow_ne_zero _ (by norm_num)) hm', Nat.primeFactors_prime_pow (by omega)
    Nat.prime_two]
theorem lemmaR2a (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {v m' : ℕ} (hv : 3 ≤ v)
    (hm : m = 2 ^ v * m') (hm'odd : m' % 2 = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : ¬ p ∣ t) (hxm : x.Coprime m) (hym : y.Coprime m)
    (hgt : m.gcd t = 2) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x)
    (hxym' : x ≡ y [MOD m']) (hg2 : x ≡ y * (1 + 2 ^ (v - 1)) [MOD 2 ^ v]) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e t = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  have hm'0 : m' ≠ 0 := by omega
  haveI : NeZero m' := ⟨hm'0⟩
  have hv1 : v = (v - 1) + 1 := by omega
  have h2v : (2 : ℕ) ^ v = 2 * 2 ^ (v - 1) := by rw [hv1, pow_succ]; simp [mul_comm]
  set f1 := 2 ^ (v - 1) * m' with hf1
  haveI : NeZero f1 := ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) hm'0⟩
  have hmf1 : m = 2 * f1 := by rw [hm, h2v, hf1]; ring
  have h4f1 : 4 ∣ f1 := dvd_mul_of_dvd_left (by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)) _
  have h2f1 : 2 ∣ f1 := dvd_trans (by norm_num) h4f1
  have hm4 : m % 4 ≠ 2 := by rw [hmf1]; omega
  have h2m : 2 ∣ m := by rw [hmf1]; exact dvd_mul_right 2 f1
  have hxodd : ¬ 2 ∣ x := fun h => by
    have := Nat.dvd_gcd h h2m; rw [hxm.gcd_eq_one] at this; omega
  have hyodd : ¬ 2 ∣ y := fun h => by
    have := Nat.dvd_gcd h h2m; rw [hym.gcd_eq_one] at this; omega
  set T := t / m.gcd t with hTdef
  have ht2 : t = 2 * T := by
    rw [hTdef, hgt]; exact (Nat.mul_div_cancel' (hgt ▸ Nat.gcd_dvd_right m t)).symm
  have hTodd : ¬ 2 ∣ T := by
    intro h
    have h4t : 4 ∣ t := by rw [ht2]; exact Nat.mul_dvd_mul_left 2 h
    have h4m : 4 ∣ m := by rw [hmf1]; exact Nat.mul_dvd_mul_left 2 h2f1
    have := Nat.dvd_gcd h4m h4t; rw [hgt] at this; omega
  have hbt : T.Coprime m := by
    have hg1 : (m / 2).gcd (t / 2) = 1 := by
      rw [Nat.gcd_div h2m (hgt ▸ Nat.gcd_dvd_right m t), hgt]
    rw [hmf1, Nat.coprime_mul_iff_right]
    refine ⟨(Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hTodd)), ?_⟩
    rw [hmf1, Nat.mul_div_cancel_left _ (by norm_num), ← hgt, ← hTdef] at hg1
    · exact Nat.coprime_comm.1 hg1
  have htm : ¬ t.Coprime m := fun h => by rw [Nat.coprime_comm] at h; rw [h] at hgt; omega
  obtain ⟨hx, hy, hsep, hN, hdie⟩ := setup3 hp7 hr a e x y t himg hpx hpy hxm hym htm hβ
  have htx : t ≠ x := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hxm)] at hgt; omega
  have hty : t ≠ y := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hym)] at hgt; omega
  have hpt' : ¬ p ∣ t := hpt
  have hTX : ((T : ℕ) : ZMod (p ^ r)) = -(x : ZMod (p ^ r)) := by
    have hs : ((x + y + t : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [ht2] at hs; push_cast at hs; rw [hβ] at hs
    have h2 : IsUnit ((2 : ℕ) : ZMod (p ^ r)) :=
      (ZMod.isUnit_iff_coprime 2 _).2 (small_cop (by norm_num) (by norm_num) hp7)
    push_cast at h2
    have := (h2.mul_right_eq_zero).1 (show (2 : ZMod (p ^ r)) * (T + x) = 0 by linear_combination hs)
    linear_combination this
  have hxyq : ¬ x ≡ y [MOD 2 ^ v] := by
    intro h
    have h1 := (h.symm.trans hg2)
    have hdvd : (2 : ℤ) ^ v ∣ (y : ℤ) * 2 ^ (v - 1) := by
      have := (Nat.modEq_iff_dvd.1 h1); push_cast at this
      have e : (y : ℤ) * (1 + 2 ^ (v - 1)) - y = y * 2 ^ (v - 1) := by ring
      rw [e] at this; exact this
    rw [show (2 : ℤ) ^ v = 2 ^ (v - 1) * 2 by rw [← pow_succ, ← hv1], mul_comm (y : ℤ)] at hdvd
    have := Int.dvd_of_mul_dvd_mul_left (pow_ne_zero _ (by norm_num)) hdvd
    exact hyodd (by exact_mod_cast this)
  have hEq := top_equal hp7 hr hpm hm4 (q := 2) (v := v) (m' := m') Nat.prime_two (by omega) hm
    (by omega) a e hP x y hx hy hxy hβ hsep hN hxym' hxyq
  have hdt : dm m t = f1 := by
    rw [dm, hgt, hmf1, Nat.mul_div_cancel_left _ (by norm_num)]
  have hw : ((m.totient : ℂ) / ((dm m t).totient : ℂ)) = 2 := by
    rw [hdt, hmf1, Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2f1]
    push_cast
    rw [mul_div_assoc, div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero
      (NeZero.ne f1))).ne'), mul_one]
  have hxy2 : x ≡ y [MOD 2 ^ (v - 1)] := by
    have h1 : y * (1 + 2 ^ (v - 1)) ≡ y [MOD 2 ^ (v - 1)] := by
      rw [Nat.modEq_iff_dvd]; push_cast; exact ⟨-(y : ℤ), by ring⟩
    exact (hg2.of_dvd (by rw [h2v]; exact dvd_mul_left _ _)).trans h1
  have hcop2 : (2 ^ (v - 1)).Coprime m' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  have hxyf1 : x ≡ y [MOD f1] := (Nat.modEq_and_modEq_iff_modEq_mul hcop2).1 ⟨hxy2, hxym'⟩
  have hTm' : ((T : ℕ) : ZMod m') = -(x : ZMod m') := by
    have hs : ((x + y + t : ℕ) : ZMod m') = 0 := by
      rw [hsum, hm, (ZMod.natCast_eq_zero_iff _ _).2 (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)]
    rw [ht2] at hs; push_cast at hs
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hxym'.symm] at hs
    have h2 : IsUnit ((2 : ℕ) : ZMod m') := (ZMod.isUnit_iff_coprime 2 _).2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    push_cast at h2
    have := (h2.mul_right_eq_zero).1 (show (2 : ZMod m') * (T + x) = 0 by linear_combination hs)
    linear_combination this
  have hfm1 : f1 ∣ m := by rw [hmf1]; exact dvd_mul_left _ _
  have hEm1 : eulerPrimes m f1 = ∅ := by
    ext ℓ
    simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hl, hld, -⟩, hn⟩
    rw [hmf1] at hld
    rcases hl.dvd_mul.1 hld with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h] at hn; exact hn h2f1
    · exact hn h
  have hEf1 : eulerPrimes f1 f1 = ∅ := by
    ext ℓ
    simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
    rintro ⟨⟨-, hld, -⟩, hn⟩; exact hn hld
  have heq1 := level_eq hp7 hr hpm a e hP (f := f1) hfm1 (by rw [hEm1]; exact empty_subset _)
    x y t hx hy hxy hβ (by rw [himg]; simp) hpt htx hty (by rw [hdt]) (by rw [hdt, hEf1, hEm1])
    hbt hTX (fun w hw h1 h2 h3 => hdie w hw h1 h2 h3)
  rw [hw] at heq1
  have hxf1 : x.Coprime f1 := hxm.coprime_dvd_right hfm1
  have hTf1 : T.Coprime f1 := hbt.coprime_dvd_right hfm1
  set zf : ZMod f1 := -(T : ZMod f1) * (x : ZMod f1)⁻¹
  set z : ℤ := (zf.val : ℤ)
  have hzx : ((z : ℤ) : ZMod f1) * (x : ZMod f1) = -(T : ZMod f1) := by
    simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val, zf, mul_assoc]
    rw [mul_comm ((x : ZMod f1))⁻¹, ZMod.coe_mul_inv_eq_one x hxf1, mul_one]
  have hm'f1 : m' ∣ f1 := dvd_mul_left _ _
  have c1 : z ≡ 1 [ZMOD m'] := by
    have h := congrArg (ZMod.castHom hm'f1 (ZMod m')) hzx
    rw [map_mul, map_intCast, map_natCast, map_neg, map_natCast, hTm', neg_neg] at h
    have hxu : IsUnit ((x : ℕ) : ZMod m') :=
      (ZMod.isUnit_iff_coprime x m').2 (hxm.coprime_dvd_right (by rw [hm]; exact dvd_mul_left _ _))
    obtain ⟨u, hu⟩ := hxu
    rw [← hu] at h
    have h1 : ((z : ℤ) : ZMod m') = 1 := by
      have := congrArg (· * ((u⁻¹ : (ZMod m')ˣ) : ZMod m')) h
      simpa [mul_assoc] using this
    rw [← ZMod.intCast_eq_intCast_iff, h1, Int.cast_one]
  set B : ℕ := 2 ^ (v - 2) with hB
  have hB1 : (2 : ℕ) ^ (v - 1) = 2 * B := by
    rw [hB, ← pow_succ']; congr 1; omega
  have hB2 : (2 : ℕ) ^ v = 4 * B := by rw [h2v, hB1]; ring
  have hint : ((2 * B : ℕ) : ℤ) ∣ (x : ℤ) * (1 + B) + T := by
    obtain ⟨k, hk⟩ : ((4 * B : ℕ) : ℤ) ∣ ((y * (1 + 2 ^ (v - 1)) : ℕ) : ℤ) - x := by
      rw [← hB2]; exact_mod_cast Nat.modEq_iff_dvd.1 hg2
    obtain ⟨s', hs'⟩ : ∃ s' : ℕ, x + y = 2 * s' := ⟨(x + y) / 2, by omega⟩
    have hsum' : ((x + y + t : ℕ) : ℤ) = ((p ^ r * (4 * B * m') : ℕ) : ℤ) := by
      rw [hsum, hm, hB2]
    refine ⟨s' - k + ((p ^ r : ℕ) : ℤ) * m', ?_⟩
    have ht2' : (t : ℤ) = 2 * T := by exact_mod_cast ht2
    have hs'' : (x : ℤ) + y = 2 * s' := by exact_mod_cast hs'
    rw [hB1] at hk
    push_cast at hk hsum' ⊢
    have h2 : (2 : ℤ) * ((x : ℤ) * (1 + B) + T) = 2 * (2 * B * (s' - k + (p : ℤ) ^ r * m')) := by
      linear_combination -hk + 2 * (B : ℤ) * hs'' + hsum' - ht2'
    exact mul_left_cancel₀ (two_ne_zero) h2
  have h2f1' : 2 ^ (v - 1) ∣ f1 := dvd_mul_right _ _
  have c2 : z ≡ 1 + 2 ^ (v - 1 - 1) [ZMOD 2 ^ (v - 1)] := by
    have h := congrArg (ZMod.castHom h2f1' (ZMod (2 ^ (v - 1)))) hzx
    rw [map_mul, map_intCast, map_natCast, map_neg, map_natCast] at h
    have hT2 : ((T : ℕ) : ZMod (2 ^ (v - 1))) = -((x : ZMod (2 ^ (v - 1))) * (1 + B)) := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ (v - 1))).2 (hB1 ▸ hint)
      push_cast at this
      linear_combination this
    rw [hT2, neg_neg] at h
    have hxu : IsUnit ((x : ℕ) : ZMod (2 ^ (v - 1))) :=
      (ZMod.isUnit_iff_coprime x _).2 (Nat.Coprime.pow_right _
        (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hxodd)))
    obtain ⟨u, hu⟩ := hxu
    rw [← hu] at h
    have h1 : ((z : ℤ) : ZMod (2 ^ (v - 1))) = 1 + (B : ZMod (2 ^ (v - 1))) := by
      have := congrArg (· * ((u⁻¹ : (ZMod (2 ^ (v - 1)))ˣ) : ZMod (2 ^ (v - 1)))) h
      simp only [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at this
      have hu1 : (u : ZMod (2 ^ (v - 1))) * ((u⁻¹ : (ZMod (2 ^ (v - 1)))ˣ) : ZMod (2 ^ (v - 1))) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [this]; linear_combination ((B : ZMod (2 ^ (v - 1))) + 1) * hu1
    rw [show v - 1 - 1 = v - 2 by omega]
    have := (ZMod.intCast_eq_intCast_iff z (1 + (B : ℤ)) (2 ^ (v - 1))).1 (by push_cast; exact h1)
    push_cast at this; exact this
  have hzne : ¬ z ≡ 1 [ZMOD (2 : ℤ) ^ (v - 1)] := by
    intro h
    have h3 := c2.symm.trans h
    rw [Int.modEq_iff_dvd] at h3
    have : (2 : ℤ) ^ (v - 1) ∣ 2 ^ (v - 1 - 1) := by
      have e : (1 : ℤ) - (1 + 2 ^ (v - 1 - 1)) = -(2 ^ (v - 1 - 1)) := by ring
      rw [e] at h3; exact (dvd_neg).1 h3
    have := Int.le_of_dvd (by positivity) this
    have : (2 : ℤ) ^ (v - 1 - 1) < 2 ^ (v - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    omega
  have hcop2' : (2 ^ (v - 1)).Coprime m' := hcop2
  have hSp : Sp f1 z := by
    rw [hf1]
    refine (Sp_mul hcop2' (pow_ne_zero _ (by norm_num)) hm'0 z).2 ⟨?_, Sp_of_one c1⟩
    rw [Sp_pp Nat.prime_two (by omega)]
    right; right; exact ⟨rfl, by omega, by exact_mod_cast c2⟩
  have htau : tau f1 z = 1 := by
    rw [hf1, tau_mul hcop2' (pow_ne_zero _ (by norm_num)) hm'0, tau_pp Nat.prime_two (by omega),
      if_neg (by exact_mod_cast hzne), tau_eq_zero c1]
  have hgu : IsUnit ((z : ℤ) : ZMod f1) := by
    have hTu : IsUnit (-(T : ZMod f1)) := ((ZMod.isUnit_iff_coprime T f1).2 hTf1).neg
    rw [← hzx] at hTu
    exact isUnit_of_mul_isUnit_left hTu
  obtain ⟨-, G2⟩ := lemmaG' (NeZero.ne f1) (by omega) hgu.unit z hgu.unit_spec.symm
  obtain ⟨η₀, hη₀⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne f1) (by omega)
  have hval := G2 hSp η₀ hη₀
  rw [htau, IsUnit.unit_spec, pow_one] at hval
  have hE1 := heq1 η₀ hη₀
  have hyx : ((y : ℕ) : ZMod f1) = x := ((ZMod.natCast_eq_natCast_iff _ _ _).2 hxyf1).symm
  have hmT : η₀ (-1) * η₀ ((T : ℕ) : ZMod f1) = -η₀ ((x : ℕ) : ZMod f1) := by
    rw [← map_mul, show (-1 : ZMod f1) * T = -(T : ZMod f1) by ring, ← hzx, map_mul, hval]; ring
  rw [hyx, hEq] at hE1
  have hηx : η₀ ((x : ℕ) : ZMod f1) ≠ 0 := by
    rw [← ZMod.coe_unitOfCoprime x hxf1]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hA : ((classSum a e x + classSum a e t : ℚ) : ℂ) * η₀ ((x : ℕ) : ZMod f1) = 0 := by
    push_cast
    have : (2 : ℂ) * (((classSum a e x : ℚ) : ℂ) + ((classSum a e t : ℚ) : ℂ)) *
        η₀ ((x : ℕ) : ZMod f1) = 0 := by
      linear_combination hE1 + 2 * ((classSum a e t : ℚ) : ℂ) * hmT
    have h2 := (mul_eq_zero.1 this).resolve_right hηx
    rw [(mul_eq_zero.1 h2).resolve_left two_ne_zero, zero_mul]
  have hsum1 : classSum a e x + classSum a e t = 0 := by
    exact_mod_cast (mul_eq_zero.1 hA).resolve_right hηx
  have hm'm : m' ∣ m := by rw [hm]; exact dvd_mul_left _ _
  have hE2' : eulerPrimes m m' ⊆ {2} := fun ℓ hl => mem_singleton.2
    (euler_sub (v := v) (v' := 0) Nat.prime_two (by rwa [pow_zero, one_mul, ← hm]))
  have hEul2 : eulerPrimes (dm m t) m' = eulerPrimes m m' := by
    rw [hdt]; unfold eulerPrimes
    rw [hf1, hm, primeFactors_two_pow_mul (by omega) hm'0, primeFactors_two_pow_mul (by omega) hm'0]
  have heq2 := level_eq hp7 hr hpm a e hP (f := m') hm'm hE2' x y t hx hy hxy hβ
    (by rw [himg]; simp) hpt htx hty (by rw [hdt]; exact hm'f1) hEul2 hbt hTX
    (fun w hw h1 h2 h3 => hdie w hw h1 h2 h3)
  rw [hw] at heq2
  obtain ⟨η₁, hη₁⟩ := Erdos634.LemmaSGprime.exists_primitive hm'0 (by omega)
  have hE2 := heq2 η₁ hη₁
  have hyx' : ((y : ℕ) : ZMod m') = x := ((ZMod.natCast_eq_natCast_iff _ _ _).2 hxym').symm
  have hmT' : η₁ (-1) * η₁ ((T : ℕ) : ZMod m') = η₁ ((x : ℕ) : ZMod m') := by
    rw [← map_mul, hTm']; congr 1; ring
  rw [hyx', hEq] at hE2
  have hηx' : η₁ ((x : ℕ) : ZMod m') ≠ 0 := by
    rw [← ZMod.coe_unitOfCoprime x (hxm.coprime_dvd_right hm'm)]
    exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hB' : ((classSum a e x - classSum a e t : ℚ) : ℂ) * η₁ ((x : ℕ) : ZMod m') = 0 := by
    push_cast
    have : (2 : ℂ) * (((classSum a e x : ℚ) : ℂ) - ((classSum a e t : ℚ) : ℂ)) *
        η₁ ((x : ℕ) : ZMod m') = 0 := by
      linear_combination hE2 + 2 * ((classSum a e t : ℚ) : ℂ) * hmT'
    have h2 := (mul_eq_zero.1 this).resolve_right hηx'
    rw [(mul_eq_zero.1 h2).resolve_left two_ne_zero, zero_mul]
  have hdiff : classSum a e x - classSum a e t = 0 := by
    exact_mod_cast (mul_eq_zero.1 hB').resolve_right hηx'
  have hx0 : classSum a e x = 0 := by linarith
  refine ⟨hx0, by rw [hEq, hx0], by linarith⟩
end R2a
end Erdos634.LemmaSR2a
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSR1p
open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum)
open Erdos634.LemmaSFC (fullPts card_N)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau Sp_pp)
open Erdos634.LemmaSGpp (SpPP)
theorem modEq_of_components {m : ℕ} (hm : m ≠ 0) {z : ℤ}
    (h : ∀ q ∈ m.primeFactors, z ≡ 1 [ZMOD (q : ℤ) ^ m.factorization q]) : z ≡ 1 [ZMOD m] := by
  rw [Int.modEq_iff_dvd, Int.natCast_dvd]
  by_cases hN : (1 - z).natAbs = 0
  · rw [hN]; exact dvd_zero _
  rw [← Nat.factorization_le_iff_dvd hm hN, Finsupp.le_def]
  intro q
  by_cases hq : q ∈ m.primeFactors
  · have hqp := Nat.prime_of_mem_primeFactors hq
    have h1 := Int.ModEq.dvd (h q hq)
    rw [show ((q : ℤ) ^ m.factorization q) = ((q ^ m.factorization q : ℕ) : ℤ) by push_cast; rfl,
      Int.natCast_dvd] at h1
    exact (hqp.pow_dvd_iff_le_factorization hN).1 h1
  · rw [Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])]; exact Nat.zero_le _
section R1p
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem lemmaR1prime (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (htpos : 0 < t) (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : p ∣ t) (hxm : x.Coprime m)
    (hym : y.Coprime m) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = -(x : ZMod (p ^ r))) :
    classSum a e x = 0 ∧ classSum a e y = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hmem : ∀ w, w ∈ univ.image a ↔ w = x ∨ w = y ∨ w = t := by
    intro w; rw [himg]; simp
  have hx : x ∈ fullPts p m a := mem_filter.2 ⟨(hmem x).2 (Or.inl rfl), hpx, hxm⟩
  have hy : y ∈ fullPts p m a := mem_filter.2 ⟨(hmem y).2 (Or.inr (Or.inl rfl)), hpy, hym⟩
  have hsub : ∀ w ∈ fullPts p m a, w = x ∨ w = y := by
    intro w hw
    have hwf := mem_filter.1 hw
    rcases (hmem w).1 hwf.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h; exact absurd hpt hwf.2.1
  have hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x := by
    intro w hw hwx hwy; rcases hsub w hw with h | h <;> contradiction
  have hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card := by
    have hc : ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card ≤ 2 := by
      refine (card_le_card (?_ : _ ⊆ ({(x : ZMod (p ^ r)), -(x : ZMod (p ^ r))} : Finset _))).trans
        ((card_insert_le _ _).trans (by simp))
      intro u hu
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hu
      rcases hsub w hw with rfl | rfl <;> simp [hβ]
    rw [card_N hr]; split_ifs <;> omega
  have hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → ¬ p ∣ w → classSum a e w ≠ 0 → False := by
    intro w hw hwx hwy hpw _
    rcases (hmem w).1 hw with h | h | h
    · exact hwx h
    · exact hwy h
    · exact hpw (h ▸ hpt)
  set z : ℤ := ((((x : ZMod m) * ((-1 : ZMod m) * (y : ZMod m))⁻¹)).val : ℤ)
  have hsyu : IsUnit ((-1 : ZMod m) * (y : ZMod m)) :=
    isUnit_one.neg.mul ((ZMod.isUnit_iff_coprime y m).2 hym)
  have hz : z * (-1 * y) ≡ x [ZMOD m] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simp only [z, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_neg, Int.cast_one]
    rw [mul_assoc, ZMod.inv_mul_of_unit _ hsyu, mul_one]
  have hkey := Erdos634.LemmaSL.fc_key hp7 hr hpm a e hP x y hx hy hxy (-1) (Or.inr rfl)
    (by rw [hβ]; push_cast; ring) hsep hN
  rcases Erdos634.LemmaSL.rel_Gprime hm4 _ _ x y hxm hym (-1) (Or.inr rfl) z hz hkey with h | ⟨hSp, -⟩
  · exact h
  have hg1 : ¬ z ≡ 1 [ZMOD m] := by
    intro h1
    have hxy0 : ((x + y : ℕ) : ZMod m) = 0 := by
      have := (ZMod.intCast_eq_intCast_iff _ _ _).2 (h1.mul_right (-1 * (y : ℤ)) |>.symm.trans hz)
      push_cast at this; push_cast; linear_combination -this
    have hxyP : ((x + y : ℕ) : ZMod (p ^ r)) = 0 := by push_cast; rw [hβ]; ring
    rw [ZMod.natCast_eq_zero_iff] at hxy0 hxyP
    have hn : p ^ r * m ∣ x + y :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (Erdos634.LemmaSPhi.cop_pr hpm) hxyP hxy0
    have := Nat.le_of_dvd (by
      rcases Nat.eq_zero_or_pos x with h | h
      · exact absurd (h ▸ dvd_zero p) hpx
      · omega) hn
    omega
  obtain ⟨q, hq, hbad⟩ : ∃ q ∈ m.primeFactors, ¬ z ≡ 1 [ZMOD (q : ℤ) ^ m.factorization q] := by
    by_contra hno; push Not at hno
    exact hg1 (modEq_of_components (NeZero.ne m) hno)
  have hqp := Nat.prime_of_mem_primeFactors hq
  set v := m.factorization q
  have hv : 1 ≤ v := (hqp.dvd_iff_one_le_factorization (NeZero.ne m)).1 (Nat.dvd_of_mem_primeFactors hq)
  have hspp : SpPP q v z := hSp q hq
  set m' := m / q ^ v
  have hmm' : m = q ^ v * m' := (Nat.ordProj_mul_ordCompl_eq_self m q).symm
  have hqm' : ¬ q ∣ m' := Nat.not_dvd_ordCompl hqp (NeZero.ne m)
  rcases hspp with h | ⟨rfl, hv1, -⟩ | ⟨rfl, hv2, -⟩
  · exact absurd h hbad
  · exact Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 3) (v := v) (v' := 0) (m' := m') (Or.inr rfl) hv
      hqm' hmm' hm4 (Or.inl rfl) a e hP x y hx hy hxy (-1) (Or.inr rfl) (by rw [hβ]; push_cast; ring)
      hsep hN z hz hbad (fun w hw h1 h2 h3 h4 _ => hdie w hw h1 h2 h3 h4)
  · rcases Nat.lt_or_ge v 3 with h3 | h3
    · exact Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 2) (v := v) (v' := 0) (m' := m') (Or.inl rfl) hv
        hqm' hmm' hm4 (Or.inl rfl) a e hP x y hx hy hxy (-1) (Or.inr rfl)
        (by rw [hβ]; push_cast; ring) hsep hN z hz hbad (fun w hw h1 h2 h3 h4 _ => hdie w hw h1 h2 h3 h4)
    · exact Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 2) (v := v) (v' := v - 1) (m' := m') (Or.inl rfl)
        hv hqm' hmm' hm4 (Or.inr ⟨rfl, rfl, h3⟩) a e hP x y hx hy hxy (-1) (Or.inr rfl)
        (by rw [hβ]; push_cast; ring) hsep hN z hz hbad (fun w hw h1 h2 h3 h4 _ => hdie w hw h1 h2 h3 h4)
end R1p
end Erdos634.LemmaSR1p
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSF3
open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum)
open Erdos634.LemmaSFC (fullPts card_N fc_isolated_img)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau)
open Erdos634.LemmaSGpp (SpPP)
section F3
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem lemmaF3same (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y l : ℕ) (himg : univ.image a = {x, y, l}) (hsum : x + y + l = p ^ r * m)
    (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hl : l ∈ fullPts p m a)
    (hxy : x ≠ y) (hxl : x ≠ l) (hyl : y ≠ l)
    (hβ : (y : ZMod (p ^ r)) = x) (hlβ : (l : ZMod (p ^ r)) ≠ x ∧ (l : ZMod (p ^ r)) ≠ -x) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e l = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hlf := mem_filter.1 hl
  have hmem : ∀ w, w ∈ univ.image a ↔ w = x ∨ w = y ∨ w = l := by
    intro w; rw [himg]; simp
  have hsub : ∀ w ∈ fullPts p m a, w = x ∨ w = y ∨ w = l := fun w hw => (hmem w).1 (mem_filter.1 hw).1
  have hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card := by
    have hc : ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card ≤ 2 := by
      refine (card_le_card (?_ : _ ⊆ ({(x : ZMod (p ^ r)), (l : ZMod (p ^ r))} : Finset _))).trans
        ((card_insert_le _ _).trans (by simp))
      intro u hu
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hu
      rcases hsub w hw with rfl | rfl | rfl <;> simp [hβ]
    rw [card_N hr]; split_ifs <;> omega
  have hEl : classSum a e l = 0 := by
    refine fc_isolated_img hp7 hr hpm hm4 a e hP l hl (fun w hw hwl _ => ?_) hN
    rcases hsub w hw with rfl | rfl | rfl
    · exact ⟨fun h => hlβ.1 h.symm, fun h => hlβ.2 (by rw [h]; ring)⟩
    · rw [hβ]; exact ⟨fun h => hlβ.1 h.symm, fun h => hlβ.2 (by rw [h]; ring)⟩
    · exact absurd rfl hwl
  refine ⟨?_, ?_, hEl⟩ <;> [skip; skip]
  all_goals
    have hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
        (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x := by
      intro w hw hwx hwy hE
      rcases hsub w hw with h | h | h
      · exact absurd h hwx
      · exact absurd h hwy
      · subst h; exact absurd hEl hE
    set z : ℤ := ((((x : ZMod m) * (y : ZMod m)⁻¹)).val : ℤ)
    have hzm : ((z : ℤ) : ZMod m) * (y : ZMod m) = x := by
      simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val, mul_assoc]
      rw [mul_comm ((y : ZMod m))⁻¹, ZMod.coe_mul_inv_eq_one y hyf.2.2, mul_one]
    have hz : z * (1 * y) ≡ x [ZMOD m] := by
      rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [one_mul]; exact hzm
    have hkey := Erdos634.LemmaSL.fc_key hp7 hr hpm a e hP x y hx hy hxy 1 (Or.inl rfl)
      (by rw [hβ]; push_cast; ring) hsep hN
    rcases Erdos634.LemmaSL.rel_Gprime hm4 _ _ x y hxf.2.2 hyf.2.2 1 (Or.inl rfl) z hz hkey with
      h | ⟨hSp, -⟩
    · first | exact h.1 | exact h.2
    exfalso
    have hg1 : ¬ z ≡ 1 [ZMOD m] := by
      intro h1
      have hxym : ((x : ℕ) : ZMod m) = y := by
        have := (ZMod.intCast_eq_intCast_iff _ _ _).2 h1
        rw [Int.cast_one] at this; rw [← hzm, this, one_mul]
      rw [ZMod.natCast_eq_natCast_iff] at hxym
      have hxyP : x ≡ y [MOD p ^ r] := ((ZMod.natCast_eq_natCast_iff _ _ _).1 hβ).symm
      have hn := (Nat.modEq_and_modEq_iff_modEq_mul (Erdos634.LemmaSPhi.cop_pr hpm)).1 ⟨hxyP, hxym⟩
      have hl0 : 0 < l := Nat.pos_of_ne_zero (fun h => hlf.2.1 (h ▸ dvd_zero p))
      have hy0 : 0 < y := Nat.pos_of_ne_zero (fun h => hyf.2.1 (h ▸ dvd_zero p))
      have hx0 : 0 < x := Nat.pos_of_ne_zero (fun h => hxf.2.1 (h ▸ dvd_zero p))
      exact hxy (Nat.ModEq.eq_of_lt_of_lt hn (by omega) (by omega))
    obtain ⟨q, hq, hbad⟩ : ∃ q ∈ m.primeFactors, ¬ z ≡ 1 [ZMOD (q : ℤ) ^ m.factorization q] := by
      by_contra hno; push Not at hno
      exact hg1 (Erdos634.LemmaSR1p.modEq_of_components (NeZero.ne m) hno)
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    have hlm : ((l : ℕ) : ZMod m) = -(y : ZMod m) * (((z : ℤ) : ZMod m) + 1) := by
      have hs : ((x + y + l : ℕ) : ZMod m) = 0 := by
        rw [hsum, (ZMod.natCast_eq_zero_iff _ _).2 (dvd_mul_left _ _)]
      push_cast at hs; rw [← hzm] at hs; linear_combination hs
    have hzq : ((z : ℤ) : ZMod q) = -1 := by
      rcases hSp q hq with h | ⟨rfl, -, h⟩ | ⟨rfl, hv2, h⟩
      · exact absurd h hbad
      · have := (ZMod.intCast_eq_intCast_iff z (-1) 3).2 h; push_cast at this; exact this
      · have h2 : z ≡ 1 [ZMOD 2] := by
          refine h.of_dvd ?_ |>.trans ?_
          · exact dvd_pow_self 2 (by omega)
          · rw [Int.modEq_iff_dvd]
            have e : (1 : ℤ) - (1 + 2 ^ (m.factorization 2 - 1)) = -(2 ^ (m.factorization 2 - 1)) := by
              ring
            rw [e]; exact (dvd_pow_self (2 : ℤ) (by omega)).neg_right
        have := (ZMod.intCast_eq_intCast_iff z 1 2).2 h2
        rw [this]; push_cast; decide
    have hlq : ((l : ℕ) : ZMod q) = 0 := by
      have := congrArg (ZMod.castHom hqm (ZMod q)) hlm
      rw [map_natCast, map_mul, map_neg, map_natCast, map_add, map_intCast, map_one, hzq] at this
      rw [this]; ring
    rw [ZMod.natCast_eq_zero_iff] at hlq
    have := Nat.dvd_gcd hlq hqm
    rw [hlf.2.2.gcd_eq_one] at this
    exact hqp.one_lt.ne' (Nat.dvd_one.1 this)
end F3
end Erdos634.LemmaSF3
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSR2b12
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit sum_indicator)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSFC (fullPts dm_eq_iff card_val_le_one card_N)
open Erdos634.LemmaSN (pred_dvd lemmaN_a lemmaN_b)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive primChar_ne_zero)
open Erdos634.LemmaSR3 (Phi2 psi_Phi2 setup3 top_equal small_cop kX_ne)
section L3
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem level2_three_anti (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    {f : ℕ} [NeZero f] (hfm : f ∣ m) (hf3 : f = 3)
    {q : ℕ} (hq : q = 2 ∨ q = 3) (hE : eulerPrimes m f ⊆ {q})
    (x y t : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x) (hxyf : x ≡ y [MOD f])
    (ht : t ∈ univ.image a) (hpt : ¬ p ∣ t) (hdt : dm m t = f) (htx : t ≠ x) (hty : t ≠ y)
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → w ≠ t → ¬ p ∣ w → classSum a e w ≠ 0 →
      ¬ f ∣ dm m w)
    (hsep : let X := (x : ZMod (p ^ r)); let Q := (q : ZMod (p ^ r));
      let T := ((t / m.gcd t : ℕ) : ZMod (p ^ r));
      X * Q ≠ X ∧ X ≠ T ∧ -X ≠ X ∧ -X * Q ≠ X ∧ -X ≠ T ∧ T * Q ≠ X ∧ -T ≠ T ∧ -T * Q = X) :
    classSum a e t = 0 ∧ classSum a e x + classSum a e y = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8⟩ := hsep
  set X : ZMod (p ^ r) := (x : ZMod (p ^ r))
  set Q : ZMod (p ^ r) := (q : ZMod (p ^ r))
  set bt := t / m.gcd t
  set T : ZMod (p ^ r) := (bt : ZMod (p ^ r))
  obtain ⟨η₀, hη₀⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne f) (by rw [hf3]; norm_num)
  have hev : η₀ (-1) = -1 := by
    rcases η₀.even_or_odd with h | h
    · exfalso
      have hno := (Erdos634.LemmaSParity.exists_even_primitive_iff (d := f) (NeZero.ne f)
        (by rw [hf3]; norm_num)).1 ⟨η₀, hη₀, h⟩
      exact hno.1 hf3
    · exact h
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  have hηev : η (-1) = -1 := by
    simp only [η, Erdos634.LemmaSG2.changeLevel_neg_one]; exact hev
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hqP : q.Coprime (p ^ r) := Nat.Coprime.pow_right r
    ((Nat.coprime_primes (by rcases hq with rfl | rfl <;> norm_num) hp.out).2 (by omega))
  have hQu : IsUnit Q := (ZMod.isUnit_iff_coprime q _).2 hqP
  set c' : ℂ := if q ∈ eulerPrimes m η.conductor then
    η.primitiveCharacter⁻¹ (q : ZMod η.conductor) else 0
  have hEul : ∀ ψ : DirichletCharacter ℂ (p ^ r),
      ∏ ℓ ∈ eulerPrimes m η.conductor,
        (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
        = 1 - ψ⁻¹ (q : ZMod (p ^ r)) * c' := by
    intro ψ
    have hE' : eulerPrimes m η.conductor ⊆ {q} := by rw [hηc]; exact hE
    rcases subset_singleton_iff.1 hE' with h0 | h1
    · rw [h0, prod_empty]; simp [c', h0]
    · rw [h1, prod_singleton]; simp [c', h1]
  set wt : ℂ := (m.totient : ℂ) / (f.totient : ℂ)
  set A : ℂ := ((classSum a e x : ℚ) : ℂ) * η.primitiveCharacter (x : ZMod η.conductor) +
    ((classSum a e y : ℚ) : ℂ) * η.primitiveCharacter (y : ZMod η.conductor)
  set B : ℂ := ((classSum a e t : ℚ) : ℂ) * wt * η.primitiveCharacter (bt : ZMod η.conductor)
  have hcomp : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Phi2 A B c' X Q T u = 0 := by
    intro ψ hψ hψo
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψo, hηev, one_mul]
    have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [regroup, sum_coe_sort (univ.image a)
      (fun w => ((classSum a e w : ℚ) : ℂ) * bracket (chi ψ η) w)] at hsum
    have hsub : ({x, y, t} : Finset ℕ) ⊆ univ.image a := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxf.1
      · exact hyf.1
      · exact ht
    rw [← sum_subset hsub (fun w hw hw' => by
      simp only [mem_insert, mem_singleton, not_or] at hw'
      obtain ⟨hwx, hwy, hwt⟩ := hw'
      by_cases hpw : p ∣ w
      · rw [bracket_p_dvd hr hpm hψ η w hpw, mul_zero]
      by_cases hEw : classSum a e w = 0
      · rw [hEw]; simp
      rw [bracket_unit hpm hψ η w hpw,
        if_neg (by rw [hηc]; exact hdie w hw hwx hwy hwt hpw hEw), mul_zero])] at hsum
    rw [sum_insert (by simp [hxy, htx.symm]), sum_insert (by simp [hty.symm]), sum_singleton]
      at hsum
    have hterm : ∀ s : ℕ, s ∈ fullPts p m a →
        bracket (chi ψ η) s = ψ (s : ZMod (p ^ r)) * η.primitiveCharacter (s : ZMod η.conductor) *
          (1 - ψ⁻¹ (q : ZMod (p ^ r)) * c') := by
      intro s hs
      have hsf := mem_filter.1 hs
      have hdm : dm m s = m := (dm_eq_iff s).2 hsf.2.2
      have hg : m.gcd s = 1 := Nat.coprime_comm.1 hsf.2.2
      rw [bracket_unit hpm hψ η s hsf.2.1, if_pos (by rw [hηc, hdm]; exact hfm), hg, Nat.div_one,
        hdm, hEul ψ,
        div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne'),
        one_mul]
    have htt : bracket (chi ψ η) t = wt * ψ T * η.primitiveCharacter (bt : ZMod η.conductor) := by
      rw [bracket_unit hpm hψ η t hpt, if_pos (by rw [hηc, hdt]), hdt]
      have hE0 : eulerPrimes f η.conductor = ∅ := by
        rw [hηc]; ext ℓ
        simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
        rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
      rw [hE0, prod_empty, mul_one]
    rw [hterm x hx, hterm y hy, htt, hβ] at hsum
    rw [psi_Phi2 ψ A B c' X Q T hQu, MulChar.inv_apply_eq_inv' ψ] at *
    simp only [A, B]
    linear_combination hsum
  obtain ⟨Qu, hQu'⟩ := id hQu
  have hY : ∀ w : ZMod (p ^ r), w * Q = X → w = -T := by
    intro w hw
    have : w * Q = -T * Q := by rw [hw, hs8]
    rw [← hQu'] at this
    exact (Units.mul_left_inj Qu).1 this
  have hsupp : ∀ v : (ZMod (p ^ r))ˣ, Phi2 A B c' X Q T v ≠ 0 →
      (v : ZMod (p ^ r)) = X ∨ (v : ZMod (p ^ r)) = -T ∨ (v : ZMod (p ^ r)) = T := by
    intro v hv
    by_contra hc; push Not at hc
    apply hv; unfold Phi2
    rw [if_neg hc.1, if_neg (fun h' => hc.2.1 (hY _ h')), if_neg hc.2.2]; ring
  set S4 : Finset (ZMod (p ^ r)) := {X, -T, T, -X}
  have h4 : S4.card ≤ 4 := by
    refine (card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    simp
  have hmapS : ∀ v : (ZMod (p ^ r))ˣ, (Phi2 A B c' X Q T v ≠ 0 ∨ Phi2 A B c' X Q T (-v) ≠ 0) →
      (v : ZMod (p ^ r)) ∈ S4 := by
    intro v hv
    simp only [S4, mem_insert, mem_singleton]
    rcases hv with h | h
    · rcases hsupp v h with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
    · rcases hsupp (-v) h with h1 | h1 | h1 <;> simp only [Units.val_neg] at h1
      · right; right; right; rw [← h1, neg_neg]
      · right; right; left; rw [← neg_neg (v : ZMod (p ^ r)), h1, neg_neg]
      · right; left; rw [← h1, neg_neg]
  have hanti : ∀ u, Phi2 A B c' X Q T u = -Phi2 A B c' X Q T (-u) := by
    rcases Nat.lt_or_ge r 2 with h1 | h2
    · obtain rfl : r = 1 := by omega
      refine Erdos634.LemmaSN.lemmaN_c _ hcomp ?_
      refine lt_of_le_of_lt ?_ (show 4 < p - 1 by omega)
      refine le_trans (card_le_card_of_injOn (fun v : (ZMod (p ^ 1))ˣ => (v : ZMod (p ^ 1)))
        (t := S4) (fun v hv => ?_) (fun v _ w _ h => Units.ext h)) h4
      have hv' := (mem_filter.1 hv).2
      apply hmapS
      by_contra hc; push Not at hc; apply hv'; rw [hc.1, hc.2, add_zero]
    · intro u
      have := lemmaN_a hr (Phi2 A B c' X Q T) (Or.inl rfl) hcomp (fun u => ?_) u
      · rw [this]; ring
      rw [card_N hr, if_neg (by omega)]
      refine lt_of_le_of_lt ?_ (show 4 < p by omega)
      refine le_trans (card_le_card_of_injOn (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)))
        (t := S4) (fun v hv => hmapS v (mem_filter.1 hv).2.2) (fun v _ w _ h => Units.ext h)) h4
  have hxP : x.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  have hbtP : bt.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      (fun h => hpt (dvd_trans h (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m t))))).symm
  set uX : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime x hxP
  set uT : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime bt hbtP
  have huX : (uX : ZMod (p ^ r)) = X := ZMod.coe_unitOfCoprime x hxP
  have huT : (uT : ZMod (p ^ r)) = T := ZMod.coe_unitOfCoprime bt hbtP
  have hA : A = 0 := by
    have h := hanti uX
    unfold Phi2 at h
    simp only [Units.val_neg, huX] at h
    rw [if_pos trivial, if_neg hs1, if_neg hs2, if_neg hs3, if_neg hs4, if_neg hs5] at h
    linear_combination h
  have hB : B = 0 := by
    have h := hanti uT
    unfold Phi2 at h
    simp only [Units.val_neg, huT, hA, zero_mul, zero_sub, mul_zero, neg_zero, zero_add] at h
    rw [if_pos trivial, if_neg hs7] at h
    linear_combination h
  have hgpos : 0 < m.gcd t := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have hbtf : bt.Coprime η.conductor := by
    rw [hηc, ← hdt]; exact (Nat.coprime_div_gcd_div_gcd hgpos).symm
  have hwt : wt ≠ 0 := div_ne_zero
    (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
    (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne f))).ne')
  have hEt : classSum a e t = 0 := by
    have := (mul_eq_zero.1 hB).resolve_right (primChar_ne_zero η bt hbtf)
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hwt
  have hxc : x.Coprime η.conductor := by rw [hηc]; exact hxf.2.2.coprime_dvd_right hfm
  have hxy' : (x : ZMod η.conductor) = (y : ZMod η.conductor) := by
    rw [ZMod.natCast_eq_natCast_iff, hηc]; exact hxyf
  simp only [A, ← hxy'] at hA
  have : ((classSum a e x + classSum a e y : ℚ) : ℂ) *
      η.primitiveCharacter (x : ZMod η.conductor) = 0 := by push_cast; linear_combination hA
  exact ⟨hEt, by exact_mod_cast (mul_eq_zero.1 this).resolve_right (primChar_ne_zero η x hxc)⟩
theorem lemmaR2b_12 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {m' : ℕ} (hm : m = 4 * m')
    (hm'3 : m' = 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : ¬ p ∣ t) (hxm : x.Coprime m) (hym : y.Coprime m)
    (hgt : m.gcd t = 4) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x)
    (hxym' : x ≡ y [MOD m']) (hxy4 : ¬ x ≡ y [MOD 4]) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e t = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  have hm'odd : m' % 2 = 1 := by omega
  have hm'0 : m' ≠ 0 := by omega
  haveI : NeZero m' := ⟨hm'0⟩
  have htm : ¬ t.Coprime m := fun h => by rw [Nat.coprime_comm] at h; rw [h] at hgt; omega
  obtain ⟨hx, hy, hsep, hN, hdie⟩ := setup3 hp7 hr a e x y t himg hpx hpy hxm hym htm hβ
  have hEq := top_equal hp7 hr hpm (by omega) (q := 2) (v := 2) (m' := m') Nat.prime_two
    (by norm_num) (by rw [hm]; norm_num) (by omega) a e hP x y hx hy hxy hβ hsep hN hxym'
    (by norm_num; exact hxy4)
  have hdt : dm m t = m' := by
    rw [dm, hgt, hm, Nat.mul_div_cancel_left _ (by norm_num)]
  have htx : t ≠ x := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hxm)] at hgt; omega
  have hty : t ≠ y := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hym)] at hgt; omega
  have hE : eulerPrimes m m' ⊆ {2} := fun ℓ hl => mem_singleton.2
    (Erdos634.LemmaSL.euler_sub (v := 2) (v' := 0) Nat.prime_two
      (by rw [pow_zero, one_mul, show (2 : ℕ) ^ 2 * m' = m by rw [hm]; norm_num]; exact hl))
  have hX : IsUnit ((x : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime x _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpx).symm)
  have hT : (x : ZMod (p ^ r)) + 2 * ((t / m.gcd t : ℕ) : ZMod (p ^ r)) = 0 := by
    have h4t : t / m.gcd t * 4 = t := by rw [hgt]; exact Nat.div_mul_cancel (hgt ▸ Nat.gcd_dvd_right m t)
    have hs : ((x + y + t : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [← h4t] at hs; push_cast at hs; rw [hβ] at hs
    have h2 : IsUnit ((2 : ℕ) : ZMod (p ^ r)) :=
      (ZMod.isUnit_iff_coprime 2 _).2 (small_cop (by norm_num) (by norm_num) hp7)
    push_cast at h2
    exact (h2.mul_right_eq_zero).1 (by linear_combination hs)
  obtain ⟨hEt, hExy⟩ := level2_three_anti hp7 hr hpm a e hP (f := m') (by rw [hm]; exact Nat.dvd_mul_left _ _)
    hm'3 (Or.inl rfl) hE x y t hx hy hxy hβ hxym'
    ((by rw [himg]; simp)) hpt hdt htx hty (fun w hw h1 h2 h4 _ _ _ => (hdie w hw h1 h2 h4).elim)
    (by
      intro X Q T
      have c1 := kX_ne hX 1 (small_cop (by norm_num) (by norm_num) hp7)
      have c2 := kX_ne hX 2 (small_cop (by norm_num) (by norm_num) hp7)
      have c3 := kX_ne hX 3 (small_cop (by norm_num) (by norm_num) hp7)
      push_cast at c1 c2 c3
      refine ⟨fun h => c1 (by linear_combination h), fun h => c3 (by linear_combination 2 * h + hT),
        fun h => c2 (by linear_combination -h), fun h => c3 (by linear_combination -h),
        fun h => c1 (by linear_combination -hT - 2 * h), fun h => c2 (by linear_combination hT - h),
        fun h => c1 (by linear_combination hT + h), by linear_combination -hT⟩)
  have hx0 : classSum a e x = 0 := by linarith
  exact ⟨hx0, by linarith, hEt⟩
end L3
end Erdos634.LemmaSR2b12
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSR1F2
open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum lemmaIso_class)
open Erdos634.LemmaSFC (fullPts card_N)
open Erdos634.LemmaSPhi (dm)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau)
open Erdos634.LemmaSGpp (SpPP)
theorem dvd_div_swap {m f g : ℕ} (hm : m ≠ 0) (hf : f ∣ m) (hg : g ∣ m) (h : f ∣ m / g) :
    g ∣ m / f := by
  obtain ⟨k, hk⟩ := h
  have hg0 : g ≠ 0 := fun h0 => by rw [h0] at hg; exact hm (Nat.eq_zero_of_zero_dvd hg)
  have hf0 : f ≠ 0 := fun h0 => by rw [h0] at hf; exact hm (Nat.eq_zero_of_zero_dvd hf)
  have : m = f * (g * k) := by
    rw [← mul_assoc, mul_comm f g, mul_assoc, ← hk, Nat.mul_div_cancel' hg]
  exact ⟨k, by rw [this, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hf0)]⟩
section R1F2
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem xy_mod_mprime {q : ℕ} (hq : q.Prime) {z : ℤ} (hSp : Sp m z)
    (h3 : q ≠ 3 → 3 ∣ m → z ≡ 1 [ZMOD 3 ^ m.factorization 3])
    (h2 : q ≠ 2 → ¬ 2 ∣ m) {x y : ℕ} (hz : z * (1 * y) ≡ x [ZMOD m]) :
    x ≡ y [MOD m / q ^ m.factorization q] := by
  have hm0 : m ≠ 0 := NeZero.ne m
  set m' := m / q ^ m.factorization q
  have hm'0 : m' ≠ 0 := by
    have := Nat.ordCompl_pos q hm0; omega
  have hm'm : m' ∣ m := Nat.ordCompl_dvd m q
  have hz1 : z ≡ 1 [ZMOD m'] := by
    refine Erdos634.LemmaSR1p.modEq_of_components hm'0 (fun ℓ hℓ => ?_)
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have hℓm : ℓ ∈ m.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hℓp, dvd_trans (Nat.dvd_of_mem_primeFactors hℓ) hm'm, hm0⟩
    have hℓq : ℓ ≠ q := by
      rintro rfl; exact Nat.not_dvd_ordCompl hq hm0 (Nat.dvd_of_mem_primeFactors hℓ)
    have hfac : m'.factorization ℓ = m.factorization ℓ := by
      simp only [m', Nat.factorization_ordCompl, Finsupp.erase_ne hℓq]
    rw [hfac]
    rcases hSp ℓ hℓm with h | ⟨rfl, hv1, -⟩ | ⟨rfl, -, -⟩
    · exact h
    · exact h3 (Ne.symm hℓq) (Nat.dvd_of_mem_primeFactors hℓm)
    · exact absurd (Nat.dvd_of_mem_primeFactors hℓm) (h2 (Ne.symm hℓq))
  have := (hz.of_dvd (by exact_mod_cast hm'm)).symm.trans ((hz1.mul_right (1 * (y : ℤ))))
  rw [one_mul, one_mul] at this
  exact Int.natCast_modEq_iff.1 this
theorem cast_rel {d : ℕ} (hd : d ∣ m) {z : ℤ} {x y : ℕ}
    (h : ((z : ℤ) : ZMod m) * (y : ZMod m) = x) : ((z : ℤ) : ZMod d) * (y : ZMod d) = x := by
  have := congrArg (ZMod.castHom hd (ZMod d)) h
  rwa [map_mul, map_intCast, map_natCast, map_natCast] at this
theorem xy_iff_z {d : ℕ} {z : ℤ} {x y : ℕ} (hy : y.Coprime d)
    (h : ((z : ℤ) : ZMod d) * (y : ZMod d) = x) : x ≡ y [MOD d] ↔ z ≡ 1 [ZMOD d] := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime y d).2 hy
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.intCast_eq_intCast_iff, ← h, ← hu, Int.cast_one]
  constructor
  · intro h1
    have := congrArg (· * ((u⁻¹ : (ZMod d)ˣ) : ZMod d)) h1
    simpa [mul_assoc] using this
  · intro h1; rw [h1, one_mul]
theorem lemmaR1F2 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y l : ℕ) (himg : univ.image a = {x, y, l}) (hsum : x + y + l = p ^ r * m)
    (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hpl : ¬ p ∣ l) (hlm : ¬ l.Coprime m)
    (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e l = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hm0 : m ≠ 0 := NeZero.ne m
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hxm := hxf.2.2
  have hym := hyf.2.2
  have hmem : ∀ w, w ∈ univ.image a ↔ w = x ∨ w = y ∨ w = l := by
    intro w; rw [himg]; simp
  have hsub : ∀ w ∈ fullPts p m a, w = x ∨ w = y := by
    intro w hw
    have hwf := mem_filter.1 hw
    rcases (hmem w).1 hwf.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h; exact absurd hwf.2.2 hlm
  have hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x := by
    intro w hw hwx hwy; rcases hsub w hw with h | h <;> contradiction
  have hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card := by
    have hc : ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card ≤ 1 := by
      refine card_le_one.2 (fun u hu v hv => ?_)
      obtain ⟨w1, hw1, rfl⟩ := mem_image.1 hu
      obtain ⟨w2, hw2, rfl⟩ := mem_image.1 hv
      rcases hsub w1 hw1 with rfl | rfl <;> rcases hsub w2 hw2 with rfl | rfl <;> simp [hβ]
    rw [card_N hr]; split_ifs <;> omega
  have hlim : l ∈ univ.image a := (hmem l).2 (Or.inr (Or.inr rfl))
  have hEl_of : classSum a e x = 0 → classSum a e y = 0 → classSum a e l = 0 := by
    intro h1 h2
    refine lemmaIso_class hp7 hr hpm a e hP l hlim hpl (fun w hw hwl _ hE => ?_)
    rcases (hmem w).1 hw with rfl | rfl | rfl
    · exact absurd h1 hE
    · exact absurd h2 hE
    · exact absurd rfl hwl
  have finish : classSum a e x = 0 ∧ classSum a e y = 0 →
      classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e l = 0 :=
    fun h => ⟨h.1, h.2, hEl_of h.1 h.2⟩
  set z : ℤ := ((((x : ZMod m) * (y : ZMod m)⁻¹)).val : ℤ)
  have hzm : ((z : ℤ) : ZMod m) * (y : ZMod m) = x := by
    simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val, mul_assoc]
    rw [mul_comm ((y : ZMod m))⁻¹, ZMod.coe_mul_inv_eq_one y hym, mul_one]
  have hz : z * (1 * y) ≡ x [ZMOD m] := by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [one_mul]; exact hzm
  have hkey := Erdos634.LemmaSL.fc_key hp7 hr hpm a e hP x y hx hy hxy 1 (Or.inl rfl)
    (by rw [hβ]; push_cast; ring) hsep hN
  rcases Erdos634.LemmaSL.rel_Gprime hm4 _ _ x y hxm hym 1 (Or.inl rfl) z hz hkey with
    h | ⟨hSp, -⟩
  · exact finish h
  have hβ1 : (y : ZMod (p ^ r)) = ((1 : ℤ) : ZMod (p ^ r)) * x := by rw [hβ]; push_cast; ring
  have hlrel : ((l : ℕ) : ZMod m) = -(y : ZMod m) * (((z : ℤ) : ZMod m) + 1) := by
    have hs : ((x + y + l : ℕ) : ZMod m) = 0 := by
      rw [hsum, (ZMod.natCast_eq_zero_iff _ _).2 (dvd_mul_left _ _)]
    push_cast at hs; rw [← hzm] at hs; linear_combination hs
  have hlreld : ∀ d, d ∣ m → ((l : ℕ) : ZMod d) = -(y : ZMod d) * (((z : ℤ) : ZMod d) + 1) := by
    intro d hd
    have := congrArg (ZMod.castHom hd (ZMod d)) hlrel
    rwa [map_natCast, map_mul, map_neg, map_natCast, map_add, map_intCast, map_one] at this
  have hdie_of : ∀ f : ℕ, f ∣ m → (¬ m.gcd l ∣ m / f) →
      ∀ w ∈ univ.image a, w ≠ x → w ≠ y → ¬ p ∣ w → classSum a e w ≠ 0 → ¬ f ∣ dm m w := by
    intro f hf hno w hw hwx hwy _ _ hfd
    rcases (hmem w).1 hw with h | h | rfl
    · exact hwx h
    · exact hwy h
    · exact hno (dvd_div_swap hm0 hf (Nat.gcd_dvd_left m w) hfd)
  have hgcd1 : m.gcd l ≠ 1 := fun h => hlm (Nat.coprime_comm.1 h)
  by_cases B3 : 3 ∣ m ∧ ¬ z ≡ 1 [ZMOD 3 ^ m.factorization 3]
  · 
    have h3m : 3 ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_three, B3.1, hm0⟩
    set v3 := m.factorization 3
    have hv3 : v3 = 1 := by
      rcases hSp 3 h3m with h | ⟨-, h, -⟩ | ⟨h, -, -⟩
      · exact absurd (by exact_mod_cast h) B3.2
      · exact h
      · norm_num at h
    set m' := m / 3 ^ v3
    have hmm' : m = 3 ^ v3 * m' := (Nat.ordProj_mul_ordCompl_eq_self m 3).symm
    have h3m' : ¬ 3 ∣ m' := Nat.not_dvd_ordCompl Nat.prime_three hm0
    have hm'm : m' ∣ m := Nat.ordCompl_dvd m 3
    by_cases hg3 : m.gcd l = 3
    · 
      have hodd : m % 2 = 1 := by
        by_contra hev
        have h2m : 2 ∣ m := by omega
        have hy2 : y.Coprime 2 := hym.coprime_dvd_right h2m
        have hx2 : x.Coprime 2 := hxm.coprime_dvd_right h2m
        have hz2 : ((z : ℤ) : ZMod 2) = 1 := by
          have hr2 := cast_rel h2m hzm
          have hxo : ¬ 2 ∣ x := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (Nat.coprime_comm.1 hx2)
          have hyo : ¬ 2 ∣ y := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (Nat.coprime_comm.1 hy2)
          have hx1 : ((x : ℕ) : ZMod 2) = 1 := by
            rw [← ZMod.natCast_mod, show x % 2 = 1 by omega]; rfl
          have hy1 : ((y : ℕ) : ZMod 2) = 1 := by
            rw [← ZMod.natCast_mod, show y % 2 = 1 by omega]; rfl
          rw [hx1, hy1, mul_one] at hr2; exact hr2
        have hl2 := hlreld 2 h2m
        rw [hz2] at hl2
        have : ((l : ℕ) : ZMod 2) = 0 := by
          rw [hl2, show (1 + 1 : ZMod 2) = 0 by decide, mul_zero]
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.dvd_gcd h2m this
        rw [hg3] at this; omega
      have hxym' := xy_mod_mprime Nat.prime_three hSp (fun h => absurd rfl h)
        (fun _ h2 => by omega) hz
      have hxy3 : ¬ x ≡ y [MOD 3] := by
        intro h
        have := (xy_iff_z (hym.coprime_dvd_right B3.1) (cast_rel B3.1 hzm)).1 h
        apply B3.2; rw [hv3, pow_one]; exact this
      exact Erdos634.LemmaSR3.lemmaR3 hp7 hr hpm (m' := m') (by rw [hmm', hv3, pow_one]) h3m' hodd a e hP x y l himg
        hsum hxf.2.1 hyf.2.1 hpl hxm hym hg3 hxy hβ hxym' hxy3
    · 
      refine finish (Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 3) (v := v3) (v' := 0) (m' := m')
        (Or.inr rfl) (by omega) h3m' hmm' hm4 (Or.inl rfl) a e hP x y hx hy hxy 1 (Or.inl rfl) hβ1
        hsep hN z hz (by exact_mod_cast B3.2) ?_)
      refine hdie_of _ (by rw [pow_zero, one_mul]; exact hm'm) (fun h => ?_)
      simp only [pow_zero, one_mul] at h
      rw [Nat.div_div_self (Nat.ordProj_dvd m 3) hm0, show m.factorization 3 = 1 from hv3,
        pow_one] at h
      rcases (Nat.dvd_prime Nat.prime_three).1 h with h | h
      · exact hgcd1 h
      · exact hg3 h
  · 
    have hg1 : ¬ z ≡ 1 [ZMOD m] := by
      intro h1
      have hxym : x ≡ y [MOD m] := (xy_iff_z hym hzm).2 h1
      have hxyP : x ≡ y [MOD p ^ r] := ((ZMod.natCast_eq_natCast_iff _ _ _).1 hβ).symm
      have hn := (Nat.modEq_and_modEq_iff_modEq_mul (Erdos634.LemmaSPhi.cop_pr hpm)).1 ⟨hxyP, hxym⟩
      have hl0 : 0 < l := Nat.pos_of_ne_zero (fun h => hpl (h ▸ dvd_zero p))
      have hy0 : 0 < y := Nat.pos_of_ne_zero (fun h => hyf.2.1 (h ▸ dvd_zero p))
      have hx0 : 0 < x := Nat.pos_of_ne_zero (fun h => hxf.2.1 (h ▸ dvd_zero p))
      exact hxy (Nat.ModEq.eq_of_lt_of_lt hn (by omega) (by omega))
    obtain ⟨q, hq, hbad⟩ : ∃ q ∈ m.primeFactors, ¬ z ≡ 1 [ZMOD (q : ℤ) ^ m.factorization q] := by
      by_contra hno; push Not at hno
      exact hg1 (Erdos634.LemmaSR1p.modEq_of_components hm0 hno)
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hq2 : q = 2 ∧ 2 ≤ m.factorization q ∧
        z ≡ 1 + 2 ^ (m.factorization q - 1) [ZMOD 2 ^ m.factorization q] := by
      rcases hSp q hq with h | ⟨rfl, -, -⟩ | h
      · exact absurd h hbad
      · exact absurd ⟨Nat.dvd_of_mem_primeFactors hq, by exact_mod_cast hbad⟩ B3
      · exact h
    obtain ⟨rfl, hv2, hzv⟩ := hq2
    have h2m : 2 ∣ m := Nat.dvd_of_mem_primeFactors hq
    set v := m.factorization 2
    set m' := m / 2 ^ v
    have hmm' : m = 2 ^ v * m' := (Nat.ordProj_mul_ordCompl_eq_self m 2).symm
    have h2m' : ¬ 2 ∣ m' := Nat.not_dvd_ordCompl Nat.prime_two hm0
    have hm'm : m' ∣ m := Nat.ordCompl_dvd m 2
    have hxym' := xy_mod_mprime Nat.prime_two hSp
      (fun _ h3 => by
        by_contra hc; exact B3 ⟨h3, by exact_mod_cast hc⟩) (fun h => absurd rfl h) hz
    have hpv : 2 ^ v ∣ m := Nat.ordProj_dvd m 2
    rcases Nat.lt_or_ge v 3 with hv3 | hv3
    · have hv : v = 2 := by omega
      by_cases hg4 : m.gcd l = 4
      · 
        have hxy4 : ¬ x ≡ y [MOD 4] := by
          intro h
          have h4 : 4 ∣ m := by rw [show (4 : ℕ) = 2 ^ v by rw [hv]; norm_num]; exact hpv
          have := (xy_iff_z (hym.coprime_dvd_right h4) (cast_rel h4 hzm)).1 h
          apply hbad
          have e : ((2 : ℕ) : ℤ) ^ m.factorization 2 = ((4 : ℕ) : ℤ) := by
            rw [show m.factorization 2 = 2 from hv]; norm_num
          rw [e]; exact this
        by_cases hm'3 : m' = 3
        · exact Erdos634.LemmaSR2b12.lemmaR2b_12 hp7 hr hpm (m' := m') (by rw [hmm', hv]; norm_num)
            hm'3 a e hP x y l himg hsum hxf.2.1 hyf.2.1 hpl hxm hym hg4 hxy hβ hxym' hxy4
        · exact Erdos634.LemmaSR3.lemmaR2b hp7 hr hpm (m' := m') (by rw [hmm', hv]; norm_num) (by omega)
            hm'3 a e hP x y l himg hsum hxf.2.1 hyf.2.1 hpl hxm hym hg4 hxy hβ hxym' hxy4
      · refine finish (Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 2) (v := v) (v' := 0) (m' := m')
          (Or.inl rfl) (by omega) h2m' hmm' hm4 (Or.inl rfl) a e hP x y hx hy hxy 1 (Or.inl rfl) hβ1
          hsep hN z hz (by exact_mod_cast hbad) ?_)
        refine hdie_of _ (by rw [pow_zero, one_mul]; exact hm'm) (fun h => ?_)
        simp only [pow_zero, one_mul] at h
        rw [Nat.div_div_self hpv hm0, hv] at h
        obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
        interval_cases i
        · exact hgcd1 (by simpa using hgi)
        · 
          have h4 : 4 ∣ m := by rw [show (4 : ℕ) = 2 ^ v by rw [hv]; norm_num]; exact hpv
          have hz4 : ((z : ℤ) : ZMod 4) = 3 := by
            have := (ZMod.intCast_eq_intCast_iff z (1 + 2 ^ (v - 1)) 4).2
              (by rw [show ((4 : ℕ) : ℤ) = 2 ^ v by rw [hv]; norm_num]; exact hzv)
            rw [this, hv]; push_cast; rfl
          have hl4 := hlreld 4 h4
          rw [hz4] at hl4
          have : ((l : ℕ) : ZMod 4) = 0 := by
            rw [hl4, show (3 + 1 : ZMod 4) = 0 by decide, mul_zero]
          rw [ZMod.natCast_eq_zero_iff] at this
          have := Nat.dvd_gcd h4 this
          rw [hgi] at this; norm_num at this
        · exact hg4 (by simpa using hgi)
    · by_cases hg2 : m.gcd l = 2
      · 
        have hg2' : x ≡ y * (1 + 2 ^ (v - 1)) [MOD 2 ^ v] := by
          have hr := cast_rel hpv hzm
          have hzz := (ZMod.intCast_eq_intCast_iff z (1 + 2 ^ (v - 1)) (2 ^ v)).2
            (by push_cast; exact hzv)
          rw [hzz] at hr
          rw [← ZMod.natCast_eq_natCast_iff, ← hr]; push_cast; ring
        exact Erdos634.LemmaSR2a.lemmaR2a hp7 hr hpm (v := v) (m' := m') hv3 hmm' (by omega) a e hP x y l himg hsum
          hxf.2.1 hyf.2.1 hpl hxm hym hg2 hxy hβ hxym' hg2'
      · refine finish (Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 2) (v := v) (v' := v - 1) (m' := m')
          (Or.inl rfl) (by omega) h2m' hmm' hm4 (Or.inr ⟨rfl, rfl, hv3⟩) a e hP x y hx hy hxy 1
          (Or.inl rfl) hβ1 hsep hN z hz (by exact_mod_cast hbad) ?_)
        have hf2 : 2 ^ (v - 1) * m' ∣ m := by
          rw [hmm']; exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by omega)) _
        refine hdie_of _ hf2 (fun h => ?_)
        have hmf : m / (2 ^ (v - 1) * m') = 2 := by
          rw [hmm', show v = (v - 1) + 1 by omega, pow_succ]
          rw [show 2 ^ (v - 1) * 2 * m' = 2 * (2 ^ (v - 1) * m') by ring]
          exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
            (fun h0 => by rw [h0, mul_zero] at hmm'; exact hm0 hmm')))
        rw [hmf] at h
        rcases (Nat.dvd_prime Nat.prime_two).1 h with h | h
        · exact hgcd1 h
        · exact hg2 h
end R1F2
end Erdos634.LemmaSR1F2
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSFCOdd
open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum)
open Erdos634.LemmaSFC (fullPts)
open Erdos634.LemmaSR3 (kX_ne small_cop)
theorem third (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, (∀ a : Fin 3 → ℕ, a i + a j + a k = a 0 + a 1 + a 2) ∧
      (∀ t : Fin 3, t = i ∨ t = j ∨ t = k) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact ⟨0, fun a => by (try simp) <;> ring, by decide⟩
    | exact ⟨1, fun a => by (try simp) <;> ring, by decide⟩
    | exact ⟨2, fun a => by (try simp) <;> ring, by decide⟩
section FC
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]
theorem fcOdd (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    (a : Fin 3 → ℕ) (hex : p = 7 → r = 1 → (m = 3 ∨ m = 4) → (fullPts p m a).card ≤ 2)
    (ha : ∀ j, 0 < a j) (hsum : a 0 + a 1 + a 2 = p ^ r * m) (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0) :
    ∀ x ∈ fullPts p m a, classSum a e x = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  intro x hx
  have hxf := mem_filter.1 hx
  have hX : IsUnit ((x : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime x _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm)
  have c1 := kX_ne hX 1 (small_cop (by norm_num) (by norm_num) hp7)
  have c2 := kX_ne hX 2 (small_cop (by norm_num) (by norm_num) hp7)
  have c3 := kX_ne hX 3 (small_cop (by norm_num) (by norm_num) hp7)
  push_cast at c1 c2 c3
  by_cases hiso : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ r)) ≠ x ∧ (y : ZMod (p ^ r)) ≠ -x
  · refine Erdos634.LemmaSFC.fc_generic hp7 hr hpm hm4 a e hP ?_ x hx hiso
    by_cases h11 : 11 ≤ p
    · exact Or.inl h11
    by_cases hr2 : 2 ≤ r
    · exact Or.inr (Or.inl hr2)
    have hp7' : p = 7 := by
      have hpp := hp.out
      interval_cases p <;> first | rfl | (exfalso; norm_num at hpp)
    have hr1 : r = 1 := by omega
    by_cases h34 : m = 3 ∨ m = 4
    · exact Or.inr (Or.inr (Or.inl (hex hp7' hr1 h34)))
    · push Not at h34
      exact Or.inr (Or.inr (Or.inr ⟨hr1, h34.1, h34.2⟩))
  push Not at hiso
  obtain ⟨y, hy, hyx, hEy, hrel⟩ := hiso
  have hyf := mem_filter.1 hy
  obtain ⟨i, -, rfl⟩ := mem_image.1 hxf.1
  obtain ⟨j, -, rfl⟩ := mem_image.1 hyf.1
  have hij : i ≠ j := fun h => hyx (by rw [h])
  obtain ⟨k, hk, hall⟩ := third i j hij
  have himg : univ.image a = {a i, a j, a k} := by
    ext w; simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨t, rfl⟩; rcases hall t with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  have hsum' : a i + a j + a k = p ^ r * m := by rw [hk a, hsum]
  have hs0 : ((a i : ℕ) : ZMod (p ^ r)) + (a j : ZMod (p ^ r)) + (a k : ZMod (p ^ r)) = 0 := by
    have : ((a i + a j + a k : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum', Nat.cast_mul, ZMod.natCast_self, zero_mul]
    push_cast at this; exact this
  by_cases hneg : ((a j : ℕ) : ZMod (p ^ r)) = -(a i : ZMod (p ^ r))
  · 
    have hpk : p ∣ a k := by
      have hk0 : ((a k : ℕ) : ZMod (p ^ r)) = 0 := by linear_combination hs0 - hneg
      rw [ZMod.natCast_eq_zero_iff] at hk0
      exact dvd_trans (dvd_pow_self p (by omega)) hk0
    exact (Erdos634.LemmaSR1p.lemmaR1prime hp7 hr hpm hm4 a e hP (a i) (a j) (a k) himg hsum' (ha k)
      hxf.2.1 hyf.2.1 hpk hxf.2.2 hyf.2.2 (Ne.symm hyx) hneg).1
  have hsame : ((a j : ℕ) : ZMod (p ^ r)) = (a i : ZMod (p ^ r)) := by
    by_contra h; exact hneg (hrel h)
  have hl : ((a k : ℕ) : ZMod (p ^ r)) = -2 * (a i : ZMod (p ^ r)) := by
    linear_combination hs0 - hsame
  have hpl : ¬ p ∣ a k := by
    intro h
    have hPk : ((a k : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    have hcast := congrArg (ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p)) hl
    rw [map_natCast, map_mul, map_neg, map_ofNat, map_natCast, hPk] at hcast
    have h2x : ((2 * a i : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hcast
    rw [ZMod.natCast_eq_zero_iff] at h2x
    rcases (Nat.Prime.dvd_mul hp.out).1 h2x with h2 | h2
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact hxf.2.1 h2
  by_cases hlc : (a k).Coprime m
  · 
    have hlfull : a k ∈ fullPts p m a := mem_filter.2 ⟨mem_image_of_mem a (mem_univ k), hpl, hlc⟩
    have hxl : a i ≠ a k := fun h => c3 (by
      have : ((a k : ℕ) : ZMod (p ^ r)) = (a i : ZMod (p ^ r)) := by rw [h]
      linear_combination hl - this)
    have hyl : a j ≠ a k := fun h => c3 (by
      have : ((a k : ℕ) : ZMod (p ^ r)) = (a i : ZMod (p ^ r)) := by rw [← h, hsame]
      linear_combination hl - this)
    exact (Erdos634.LemmaSF3.lemmaF3same hp7 hr hpm hm4 a e hP (a i) (a j) (a k) himg hsum' hx hy
      hlfull (Ne.symm hyx) hxl hyl hsame
      ⟨fun h => c3 (by linear_combination hl - h), fun h => c1 (by linear_combination hl - h)⟩).1
  · 
    exact (Erdos634.LemmaSR1F2.lemmaR1F2 hp7 hr hpm hm4 a e hP (a i) (a j) (a k) himg hsum' hx hy
      hpl hlc (Ne.symm hyx) hsame).1
end FC
end Erdos634.LemmaSFCOdd
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSR
open Erdos634.LemmaS
theorem class_zero {M : Type*} [AddCommGroup M] [Module ℚ M] (I : Finset (Fin 3)) (a : Fin 3 → ℕ)
    (e : Fin 3 → ℚ) (hcl : ∀ j ∈ I, ∑ k ∈ I.filter (fun k => a k = a j), e k = 0)
    (w : Fin 3 → M) (hw : ∀ j k, a j = a k → w j = w k) :
    ∑ j ∈ I, e j • w j = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem a hx)]
  refine sum_eq_zero (fun v hv => ?_)
  obtain ⟨j0, hj0, rfl⟩ := mem_image.1 hv
  rw [sum_congr rfl (fun j hj => by rw [hw j j0 (mem_filter.1 hj).2]), ← sum_smul, hcl j0 hj0,
    zero_smul]
theorem saw_eq_zero_imp {n m : ℕ} (hm : 0 < m) (hmn : m < n) (h : saw ((m : ℚ) / n) = 0) :
    2 * m = n := by
  unfold saw at h
  have hn : (0 : ℚ) < n := by exact_mod_cast (lt_trans hm hmn)
  have hf : Int.fract ((m : ℚ) / n) = (m : ℚ) / n := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, (div_lt_one hn).mpr (by exact_mod_cast hmn)⟩
  have hne : (m : ℚ) / n ≠ 0 := div_ne_zero (by exact_mod_cast hm.ne') hn.ne'
  rw [hf, if_neg hne] at h
  have : (2 * m : ℚ) = n := by field_simp at h; linarith
  exact_mod_cast this
theorem lemmaR {n p : ℕ} (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hp : p.Prime) (hpn : p ∣ n)
    (hP : ∀ e ∈ relSpace n a, ∀ j, ¬ p ∣ a j →
      ∑ k ∈ (univ.filter (fun k => ¬ p ∣ a k)).filter (fun k => a k = a j), e k = 0) :
    relSpace n a = trivSpace n a := by
  classical
  refine le_antisymm ?_ (trivSpace_le n a)
  intro e he
  set I := univ.filter (fun j : Fin 3 => ¬ p ∣ a j) with hI
  have hcl : ∀ j ∈ I, ∑ k ∈ I.filter (fun k => a k = a j), e k = 0 :=
    fun j hj => hP e he j (mem_filter.1 hj).2
  have hs3 : a 0 + a 1 + a 2 = n := by simpa [Fin.sum_univ_three] using hsum
  have hlt : ∀ i, a i < n := by
    intro i; have := hpos 0; have := hpos 1; have := hpos 2
    fin_cases i <;> simp <;> omega
  have hatmost : ∀ l l', l ∉ I → l' ∉ I → l = l' := by
    intro l l' hl hl'
    by_contra hne
    have hl1 : p ∣ a l := by simpa [hI] using hl
    have hl2 : p ∣ a l' := by simpa [hI] using hl'
    have hall : ∀ i, p ∣ a i := by
      intro i
      by_cases h1 : i = l
      · rw [h1]; exact hl1
      by_cases h2 : i = l'
      · rw [h2]; exact hl2
      have huniv : ({l, l', i} : Finset (Fin 3)) = univ := by
        apply Finset.eq_univ_of_card
        rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
        all_goals first
          | rfl
          | (simp only [mem_insert, mem_singleton, not_or]
             (try constructor) <;> intro h <;> subst h <;> simp_all)
      have hsum' : a l + a l' + a i = n := by
        rw [← hsum, ← huniv, sum_insert, sum_insert, sum_singleton]
        · ring
        all_goals first
          | rfl
          | (simp only [mem_insert, mem_singleton, not_or]
             (try constructor) <;> intro h <;> subst h <;> simp_all)
      have : p ∣ a l + a l' + a i := hsum' ▸ hpn
      exact (Nat.dvd_add_right (dvd_add hl1 hl2)).1 this
    have : p ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
      Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))
    rw [hgcd] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  let repv : ℕ → Fin 3 := fun v =>
    if h : (I.filter (fun m => a m = v)).Nonempty then (I.filter (fun m => a m = v)).min' h else 0
  have hrep : ∀ j ∈ I, repv (a j) ∈ I ∧ a (repv (a j)) = a j := by
    intro j hj
    have hne : (I.filter (fun m => a m = a j)).Nonempty := ⟨j, mem_filter.2 ⟨hj, rfl⟩⟩
    have := min'_mem _ hne
    simp only [repv, dif_pos hne]
    exact mem_filter.1 this
  have hdec : e = ∑ j ∈ I, e j • ((Pi.single j 1 : Fin 3 → ℚ) - Pi.single (repv (a j)) 1)
      + ∑ j ∈ I, e j • (Pi.single (repv (a j)) 1 : Fin 3 → ℚ)
      + ∑ j ∈ univ.filter (fun j => ¬ ¬ p ∣ a j), e j • (Pi.single j 1 : Fin 3 → ℚ) := by
    rw [← sum_add_distrib]
    simp only [smul_sub, sub_add_cancel]
    rw [hI, sum_filter_add_sum_filter_not]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hmid : ∑ j ∈ I, e j • (Pi.single (repv (a j)) 1 : Fin 3 → ℚ) = 0 :=
    class_zero I a e hcl (fun j => (Pi.single (repv (a j)) 1 : Fin 3 → ℚ))
      (fun j k hjk => by simp only [hjk])
  rw [hdec, hmid, add_zero]
  refine Submodule.add_mem _ (Submodule.sum_mem _ (fun j hj => ?_)) (Submodule.sum_mem _ (fun j hj => ?_))
  · 
    obtain ⟨_, hra⟩ := hrep j hj
    by_cases hjr : j = repv (a j)
    · rw [← hjr, sub_self, smul_zero]; exact Submodule.zero_mem _
    · exact pair_mem hjr hra.symm (e j)
  · 
    have hjI : j ∉ I := by simpa [hI] using hj
    have hsing : univ.filter (fun m : Fin 3 => ¬ ¬ p ∣ a m) = {j} := by
      rw [eq_singleton_iff_unique_mem]
      exact ⟨hj, fun x hx => hatmost x j (by simpa [hI] using hx) hjI⟩
    have hk1 := (mem_relSpace.1 he) 1 (Nat.coprime_one_left n)
    simp only [one_mul] at hk1
    have hIpart : ∑ i ∈ I, e i • saw ((a i : ℕ) / (n : ℚ)) = 0 :=
      class_zero I a e hcl (fun i => saw ((a i : ℕ) / (n : ℚ))) (fun i k hik => by simp only [hik])
    have hsplit := sum_filter_add_sum_filter_not univ (fun m : Fin 3 => ¬ p ∣ a m)
      (fun i => saw ((a i : ℕ) / (n : ℚ)) * e i)
    rw [hk1, hsing, sum_singleton, ← hI] at hsplit
    have hI' : ∑ i ∈ I, saw ((a i : ℕ) / (n : ℚ)) * e i = 0 := by
      rw [← hIpart]; exact sum_congr rfl (fun i _ => by rw [smul_eq_mul, mul_comm])
    rw [hI', zero_add] at hsplit
    rcases mul_eq_zero.1 hsplit with h0 | h0
    · exact half_mem (saw_eq_zero_imp (hpos j) (hlt j) h0) (e j)
    · rw [h0, zero_smul]; exact Submodule.zero_mem _
end Erdos634.LemmaSR
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSOdd
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.LemmaSElim (classSum lemmaElim)
open Erdos634.LemmaSFC (fullPts dm_eq_iff)
open Erdos634.LemmaSPhi (dm)
open Erdos634.LemmaSIso (fpc)
theorem lemmaS_odd {p r m : ℕ} [hp : Fact p.Prime] [NeZero m] (hp7 : 7 ≤ p) (hr : 1 ≤ r)
    (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    (a : Fin 3 → ℕ) (hex : p = 7 → r = 1 → (m = 3 ∨ m = 4) → (fullPts p m a).card ≤ 2) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = p ^ r * m)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (p ^ r * m) a = trivSpace (p ^ r * m) a := by
  haveI : NeZero (p ^ r * m) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m)⟩
  have hsum3 : a 0 + a 1 + a 2 = p ^ r * m := by rw [← hsum, Fin.sum_univ_three]
  have hgcd' : univ.gcd a = 1 := by
    apply Nat.eq_one_of_dvd_one
    rw [← hgcd]
    exact Nat.dvd_gcd (Finset.gcd_dvd (mem_univ 0))
      (Nat.dvd_gcd (Finset.gcd_dvd (mem_univ 1)) (Finset.gcd_dvd (mem_univ 2)))
  refine Erdos634.LemmaSR.lemmaR a hpos hsum hgcd hp.out
    (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m) (fun e he j hpj => ?_)
  have hcrit := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he
  have hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * Erdos634.LemmaSC.bracket χ (a j) = 0 := fun χ ho _ => hcrit χ ho
  have hfpc : fpc m = m := by unfold fpc; rw [if_neg hm4]
  have hall := lemmaElim hp7 hr hpm a e hsum3 hgcd' hP (fun x hx hpx hfull => by
    rw [hfpc] at hfull
    have hdm : dm m x = m := Nat.dvd_antisymm (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m x)) hfull
    exact Erdos634.LemmaSFCOdd.fcOdd hp7 hr hpm hm4 a hex hpos hsum3 e hP x
      (mem_filter.2 ⟨hx, hpx, (dm_eq_iff x).1 hdm⟩)) (a j) (mem_image_of_mem a (mem_univ j)) hpj
  unfold classSum at hall
  rw [filter_filter]
  rw [← hall]
  refine sum_congr ?_ (fun _ _ => rfl)
  ext k
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rw [h]; exact hpj, h⟩
end Erdos634.LemmaSOdd
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSOddAll
open Erdos634.LemmaS (relSpace trivSpace mem_relSpace_Z sawZ trivSpace_le)
open Erdos634.LemmaSFC (fullPts)
def L21 : List (ℕ × ℕ) :=
  [(1, 4), (1, 16), (4, 1), (4, 16), (16, 1), (16, 4), (2, 8), (2, 11), (8, 2), (8, 11), (11, 2),
    (11, 8)]
def ok21 (x y : ℕ) : Bool :=
  !(decide (x + y ≤ 21) && x % 3 != 0 && x % 7 != 0 && y % 3 != 0 && y % 7 != 0 &&
    (21 - x - y) % 3 != 0 && (21 - x - y) % 7 != 0 && x != y && x != 21 - x - y && y != 21 - x - y)
  || decide ((x, y) ∈ L21)
theorem chk21 : (List.range 22).all (fun x => (List.range 22).all (fun y => ok21 x y)) = true := by
  decide
theorem enum21 (x y z : ℕ) (hx : x % 3 ≠ 0 ∧ x % 7 ≠ 0) (hy : y % 3 ≠ 0 ∧ y % 7 ≠ 0)
    (hz : z % 3 ≠ 0 ∧ z % 7 ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs : x + y + z = 21) : (x, y) ∈ L21 := by
  have hz' : z = 21 - x - y := by omega
  subst hz'
  have h := List.all_eq_true.1 (List.all_eq_true.1 chk21 x (List.mem_range.2 (by omega))) y
    (List.mem_range.2 (by omega))
  simp only [ok21, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with h | h
  · exfalso
    simp [hx.1, hx.2, hy.1, hy.2, hz.1, hz.2, hxy, hxz, hyz, show x + y ≤ 21 by omega] at h
  · exact h
theorem rel21 (a : Fin 3 → ℕ) (h : (a 0, a 1) ∈ L21) (hs : a 0 + a 1 + a 2 = 21) :
    relSpace 21 a = trivSpace 21 a := by
  refine le_antisymm (fun e he => ?_) (trivSpace_le 21 a)
  have h1 := (mem_relSpace_Z (n := 21) (by norm_num)).1 he 1 (by norm_num)
  have h2 := (mem_relSpace_Z (n := 21) (by norm_num)).1 he 2 (by norm_num)
  have h5 := (mem_relSpace_Z (n := 21) (by norm_num)).1 he 5 (by norm_num)
  simp only [L21, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
  have hz : e = 0 := by
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
      ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    · have hc : a 2 = 21 - a 0 - a 1 := by omega
      rw [ha, hb] at hc
      norm_num at hc
      rw [ha, hb, hc] at h1 h2 h5
      simp only [sawZ] at h1 h2 h5
      norm_num at h1 h2 h5
      funext i
      fin_cases i <;> simp <;> linarith
  rw [hz]; exact zero_mem _
theorem lemmaS_oddAll {p r m : ℕ} [hp : Fact p.Prime] [NeZero m] (hp7 : 7 ≤ p) (hr : 1 ≤ r)
    (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = p ^ r * m)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (p ^ r * m) a = trivSpace (p ^ r * m) a := by
  by_cases hE : p = 7 ∧ r = 1 ∧ (m = 3 ∨ m = 4) ∧ ¬ (fullPts p m a).card ≤ 2
  · obtain ⟨rfl, rfl, hm34, hc⟩ := hE
    have himg3 : (univ.image a).card ≤ 3 := card_image_le.trans (by simp)
    have hsub : fullPts 7 m a ⊆ univ.image a := filter_subset _ _
    have hfc := card_le_card hsub
    have heq : fullPts 7 m a = univ.image a := eq_of_subset_of_card_le hsub (by omega)
    have hall : ∀ i, a i ∈ fullPts 7 m a := fun i => heq ▸ mem_image_of_mem a (mem_univ i)
    have hinj : Set.InjOn a (univ : Finset (Fin 3)) :=
      card_image_iff.1 (by rw [card_univ, Fintype.card_fin]; omega)
    have hne : ∀ i j : Fin 3, i ≠ j → a i ≠ a j :=
      fun i j hij h => hij (hinj (mem_coe.2 (mem_univ i)) (mem_coe.2 (mem_univ j)) h)
    have hcond : ∀ i, ¬ 7 ∣ a i ∧ (a i).Coprime m := fun i => (mem_filter.1 (hall i)).2
    have hsum3 : a 0 + a 1 + a 2 = 7 ^ 1 * m := by rw [← hsum, Fin.sum_univ_three]
    rcases hm34 with rfl | rfl
    · 
      have hmod : ∀ i, a i % 3 ≠ 0 ∧ a i % 7 ≠ 0 := by
        intro i
        obtain ⟨h7, h3⟩ := hcond i
        refine ⟨fun h => ?_, fun h => h7 (Nat.dvd_of_mod_eq_zero h)⟩
        have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) (dvd_refl 3)
        rw [h3.gcd_eq_one] at this; omega
      have hs21 : a 0 + a 1 + a 2 = 21 := by rw [hsum3]; norm_num
      have := enum21 (a 0) (a 1) (a 2) (hmod 0) (hmod 1) (hmod 2) (hne 0 1 (by simp))
        (hne 0 2 (by simp)) (hne 1 2 (by simp)) hs21
      show relSpace 21 a = trivSpace 21 a
      exact rel21 a this hs21
    · 
      exfalso
      have hodd : ∀ i, a i % 2 = 1 := by
        intro i
        by_contra h
        have h2 : 2 ∣ a i := by omega
        have := Nat.dvd_gcd h2 (show 2 ∣ 4 by norm_num)
        rw [(hcond i).2.gcd_eq_one] at this; omega
      have := hodd 0; have := hodd 1; have := hodd 2
      omega
  · exact Erdos634.LemmaSOdd.lemmaS_odd hp7 hr hpm hm4 a
      (fun h1 h2 h3 => by by_contra hc; exact hE ⟨h1, h2, h3, hc⟩) hpos hsum hgcd
end Erdos634.LemmaSOddAll
end

section
namespace Erdos634.LemmaSEvenT
section
variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]
noncomputable def Phi5 (c1 c2 c3 z : ℂ) (w y y' V : R) (u : R) : ℂ :=
  (if u = 2 * w then c1 else 0) + (if u = w then -z * c1 else 0) + (if u = y then c2 else 0) +
    (if u = y' then -z * c2 else 0) + (if u = V then c3 else 0)
theorem nek {w a b c : R} (hw : IsUnit w) (hc : IsUnit c) (h : a - b = c * w) : a ≠ b := by
  intro hab; rw [hab, sub_self] at h; exact (hc.mul hw).ne_zero h.symm
theorem small_units (u2 : IsUnit (2 : R)) (u3 : IsUnit (3 : R)) (u5 : IsUnit (5 : R)) :
    IsUnit (4 : R) ∧ IsUnit (6 : R) ∧ IsUnit (8 : R) ∧ IsUnit (9 : R) ∧ IsUnit (10 : R) ∧
      IsUnit (12 : R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := u2.mul u2; norm_num at this; exact this
  · have := u2.mul u3; norm_num at this; exact this
  · have := (u2.mul u2).mul u2; norm_num at this; exact this
  · have := u3.mul u3; norm_num at this; exact this
  · have := u2.mul u5; norm_num at this; exact this
  · have := (u2.mul u2).mul u3; norm_num at this; exact this
end
section
variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]
set_option maxHeartbeats 4000000 in
theorem key1 {w y y' V : R} {c1 c2 c3 z s : ℂ} (u2 : IsUnit (2 : R)) (u3 : IsUnit (3 : R))
    (u5 : IsUnit (5 : R)) (hrel : 2 * w + y + 2 * V = 0) (hy' : 2 * y' = y) (hw : IsUnit w)
    (hz : z ≠ 0)
    (hsym : ∀ u, IsUnit u → Phi5 c1 c2 c3 z w y y' V u = s * Phi5 c1 c2 c3 z w y y' V (-u))
    (hne1 : y ≠ 2 * w) (hne2 : y ≠ -(2 * w)) : c1 = 0 := by
  obtain ⟨k4, k6, k8, k9, k10, k12⟩ := small_units u2 u3 u5
  have k2 := u2; have k3 := u3; have k5 := u5
  by_cases hA : y = 4 * w
  · subst hA
    obtain rfl : y' = 2 * w := u2.mul_left_cancel (by rw [hy']; ring)
    obtain rfl : V = -3 * w := u2.mul_left_cancel (by linear_combination hrel)
    have E := hsym w hw
    simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] at E
    have h : z * c1 = 0 := by linear_combination -E
    exact (mul_eq_zero.1 h).resolve_left hz
  by_cases hC : y = -4 * w
  · subst hC
    obtain rfl : y' = -2 * w := u2.mul_left_cancel (by rw [hy']; ring)
    obtain rfl : V = 1 * w := u2.mul_left_cancel (by linear_combination hrel)
    have E1 := hsym (2 * w) (u2.mul hw)
    have E2 := hsym (-4 * w) (k4.neg.mul hw)
    simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] at E1 E2
    linear_combination E1 - s * z * E2
  by_cases hB : y = -6 * w
  · subst hB
    obtain rfl : y' = -3 * w := u2.mul_left_cancel (by rw [hy']; ring)
    obtain rfl : V = 2 * w := u2.mul_left_cancel (by linear_combination hrel)
    by_cases h7 : (7 : R) = 0
    · have h76 : w = -6 * w := by linear_combination w * h7
      have E1 := hsym w hw
      have E2 := hsym (-3 * w) (k3.neg.mul hw)
      simp only [Phi5, if_pos h76] at E1
      simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] at E1 E2
      have h2 : z * c2 = 0 := by linear_combination -E2
      have hc2 : c2 = 0 := (mul_eq_zero.1 h2).resolve_left hz
      have h1 : z * c1 = 0 := by linear_combination -E1 + hc2
      exact (mul_eq_zero.1 h1).resolve_left hz
    · have h76 : ¬ (w = -6 * w) := by
        intro h
        apply h7
        have h' : (7 : R) * w = 0 := by linear_combination h
        obtain ⟨uw, rfl⟩ := hw
        have := congrArg (· * ((uw⁻¹ : Rˣ) : R)) h'
        simpa [mul_assoc] using this
      have E1 := hsym w hw
      simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] at E1
      have h1 : z * c1 = 0 := by linear_combination -E1
      exact (mul_eq_zero.1 h1).resolve_left hz
  · 
    have h1 : ¬ (2 * w = y) := fun h => hne1 h.symm
    have h2 : ¬ (2 * w = y') := fun h => hA (by rw [← hy', ← h]; ring)
    have h3 : ¬ (2 * w = V) := fun h => hB (by linear_combination hrel + 2 * h)
    have h4 : ¬ (-(2 * w) = y) := fun h => hne2 h.symm
    have h5 : ¬ (-(2 * w) = y') := fun h => hC (by rw [← hy', ← h]; ring)
    have h6 : ¬ (-(2 * w) = V) := fun h => hne1 (by linear_combination hrel + 2 * h)
    have E := hsym (2 * w) (u2.mul hw)
    simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] at E
    linear_combination E
theorem Phi5_swap (c1 c2 c3 z : ℂ) (w y y' V : R) (hy' : 2 * y' = y) (u : R) :
    Phi5 c2 c1 c3 z y' (2 * w) w V u = Phi5 c1 c2 c3 z w y y' V u := by
  unfold Phi5; rw [hy']; ring
set_option maxHeartbeats 4000000 in
theorem theoremT {w y y' V : R} {c1 c2 c3 z s : ℂ} (u2 : IsUnit (2 : R)) (u3 : IsUnit (3 : R))
    (u5 : IsUnit (5 : R)) (hrel : 2 * w + y + 2 * V = 0) (hy' : 2 * y' = y) (hz : z ≠ 0)
    (hc1 : c1 ≠ 0 → IsUnit w) (hc2 : c2 ≠ 0 → IsUnit y') (hc3 : c3 ≠ 0 → IsUnit V)
    (hsym : ∀ u, IsUnit u → Phi5 c1 c2 c3 z w y y' V u = s * Phi5 c1 c2 c3 z w y y' V (-u)) :
    c3 = 0 ∧ ((c1 = 0 ∧ c2 = 0) ∨ (y = 2 * w ∧ c1 + c2 = 0) ∨ (y = -(2 * w) ∧ c1 = s * c2)) := by
  obtain ⟨k4, k6, k8, k9, k10, k12⟩ := small_units u2 u3 u5
  have k2 := u2; have k3 := u3; have k5 := u5
  have K1 : c1 ≠ 0 → y = 2 * w ∨ y = -(2 * w) := by
    intro h
    by_contra hc
    push Not at hc
    exact h (key1 u2 u3 u5 hrel hy' (hc1 h) hz hsym hc.1 hc.2)
  have K2 : c2 ≠ 0 → y = 2 * w ∨ y = -(2 * w) := by
    intro h
    by_contra hc
    push Not at hc
    apply h
    refine key1 (c2 := c1) (y := 2 * w) (y' := w) (V := V) (s := s) u2 u3 u5
      (by rw [← hy'] at hrel; linear_combination hrel) rfl (hc2 h) hz
      (fun u hu => by rw [Phi5_swap _ _ _ _ _ _ _ _ hy', Phi5_swap _ _ _ _ _ _ _ _ hy']; exact hsym u hu)
      (fun h' => hc.1 (by rw [← hy']; linear_combination -h'))
      (fun h' => hc.2 (by rw [← hy']; linear_combination h'))
  by_cases h12 : c1 = 0 ∧ c2 = 0
  · refine ⟨?_, Or.inl h12⟩
    by_contra h3
    have hw := hc3 h3
    have E := hsym V hw
    obtain ⟨rfl, rfl⟩ := h12
    simp only [Phi5, mul_zero, neg_zero, ite_self, zero_add] at E
    simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] at E
    exact h3 (by linear_combination E)
  · have hcase : y = 2 * w ∨ y = -(2 * w) := by
      by_cases h1 : c1 = 0
      · exact K2 (fun h2 => h12 ⟨h1, h2⟩)
      · exact K1 h1
    have hw : IsUnit w := by
      by_cases h1 : c1 = 0
      · have hy := hc2 (fun h2 => h12 ⟨h1, h2⟩)
        rcases hcase with h | h
        · have : y' = w := u2.mul_left_cancel (by rw [hy', h])
          rw [← this]; exact hy
        · have : y' = -w := u2.mul_left_cancel (by rw [hy', h]; ring)
          have := hy.neg; rw [‹y' = -w›, neg_neg] at this; exact this
      · exact hc1 h1
    rcases hcase with rfl | rfl
    · obtain rfl : y' = 1 * w := u2.mul_left_cancel (by rw [hy']; ring)
      obtain rfl : V = -2 * w := u2.mul_left_cancel (by linear_combination hrel)
      have E1 := hsym w hw
      have E2 := hsym (-2 * w) (k2.neg.mul hw)
      simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] at E1 E2
      have hsum : c1 + c2 = 0 := by
        have : z * (c1 + c2) = 0 := by linear_combination -E1
        exact (mul_eq_zero.1 this).resolve_left hz
      exact ⟨by linear_combination E2 + s * hsum, Or.inr (Or.inl ⟨rfl, hsum⟩)⟩
    · obtain rfl : y' = -w := u2.mul_left_cancel (by rw [hy']; ring)
      obtain rfl : V = 0 := u2.mul_left_cancel (by linear_combination hrel)
      have h3 : c3 = 0 := by
        by_contra h; exact not_isUnit_zero (hc3 h)
      have E := hsym (2 * w) (u2.mul hw)
      subst h3
      simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] at E
      exact ⟨rfl, Or.inr (Or.inr ⟨rfl, by linear_combination E⟩)⟩
end
end Erdos634.LemmaSEvenT
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSEvenComp
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit sum_indicator)
open Erdos634.LemmaSN (pred_dvd lemmaN_a lemmaN_b lemmaN_c)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive)
open Erdos634.LemmaSEvenT (Phi5)
theorem primChar_lift' {f m : ℕ} [NeZero f] [NeZero m] (h : f ∣ m) (η₀ : DirichletCharacter ℂ f)
    (b : ℕ) (hb : b.Coprime f) :
    (changeLevel h η₀).primitiveCharacter (b : ZMod (changeLevel h η₀).conductor) = η₀ (b : ZMod f) := by
  obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime b hb)
  set c := (U : ZMod m).val
  have hc : c.Coprime m := ZMod.val_coe_unit_coprime U
  have hcb : (c : ZMod f) = (b : ZMod f) := by
    have := congrArg Units.val hU
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at this
    rw [← this]; simp only [c]; rw [ZMod.natCast_val]
  have hcond : (changeLevel h η₀).conductor ∣ f := conductor_dvd_of_mem_conductorSet _ ⟨h, η₀, rfl⟩
  have h1 : ((c : ℕ) : ZMod (changeLevel h η₀).conductor) = (b : ZMod _) := by
    rw [ZMod.natCast_eq_natCast_iff] at hcb ⊢; exact hcb.of_dvd hcond
  rw [← h1, Erdos634.LemmaSL.primChar_lift h η₀ c hc, hcb]
theorem small_cop {p r k : ℕ} (hp : p.Prime) (hk : 0 < k) (hk7 : k < 7) (hp7 : 7 ≤ p) :
    k.Coprime (p ^ r) :=
  Nat.Coprime.pow_right r (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
    (fun h => by have := Nat.le_of_dvd hk h; omega)))
theorem isUnit_small {p r k : ℕ} (hp : p.Prime) (hk : 0 < k) (hk7 : k < 7) (hp7 : 7 ≤ p) :
    IsUnit ((k : ℕ) : ZMod (p ^ r)) :=
  (ZMod.isUnit_iff_coprime k (p ^ r)).2 (small_cop hp hk hk7 hp7)
section Top
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']
theorem top_term (hpm : ¬ p ∣ m) (hm : m = 2 * m') (hodd : m' % 2 = 1) (hdvd : m' ∣ m)
    {ψ : DirichletCharacter ℂ (p ^ r)} (hψ : ψ.IsPrimitive) {η : DirichletCharacter ℂ m'}
    (hη : η.IsPrimitive) (a : ℕ) (hpa : ¬ p ∣ a) :
    bracket (chi ψ (changeLevel hdvd η)) a =
      if a.Coprime m' then
        (if a % 2 = 1 then ψ (a : ZMod (p ^ r)) * η (a : ZMod m') * (1 - ψ⁻¹ 2 * (η 2)⁻¹)
          else ψ ((a / 2 : ℕ) : ZMod (p ^ r)) * η ((a / 2 : ℕ) : ZMod m'))
      else 0 := by
  set η' := changeLevel hdvd η
  have hc : η'.conductor = m' := conductor_changeLevel_of_isPrimitive hdvd hη
  rw [bracket_unit hpm hψ η' a hpa]
  have hm'0 : 0 < m' := Nat.pos_of_ne_zero (NeZero.ne m')
  have h2m' : (2 : ℕ).Coprime m' := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
  by_cases hcop : a.Coprime m'
  · rw [if_pos hcop]
    by_cases ha : a % 2 = 1
    · rw [if_pos ha]
      have hg : m.gcd a = 1 := by
        rw [hm, Nat.gcd_comm]
        exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 (Nat.odd_iff.2 ha)) hcop
      have hdm : dm m a = m := by simp [dm, hg]
      rw [if_pos (by rw [hc, hdm, hm]; exact Dvd.intro_left 2 rfl)]
      have hE : eulerPrimes (dm m a) η'.conductor = {2} := by
        rw [hdm, hc]
        ext ℓ; simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, mem_singleton]
        constructor
        · rintro ⟨⟨hl, hlm, -⟩, hlm'⟩
          rw [hm] at hlm
          rcases (Nat.Prime.dvd_mul hl).1 hlm with h2 | h2
          · exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h2
          · exact absurd h2 hlm'
        · rintro rfl
          exact ⟨⟨Nat.prime_two, by rw [hm]; exact dvd_mul_right 2 m', NeZero.ne m⟩,
            fun h => by omega⟩
      have hT : (m.totient : ℂ) / (dm m a).totient = 1 := by
        rw [hdm]; exact div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
      rw [hE, prod_singleton, hT, hg, Nat.div_one, primChar_lift' hdvd η a hcop,
        MulChar.inv_apply_eq_inv' η'.primitiveCharacter, primChar_lift' hdvd η 2 h2m']
      simp only [Nat.cast_ofNat, MulChar.inv_apply_eq_inv']
      ring
    · rw [if_neg ha]
      have ha2 : a = 2 * (a / 2) := by omega
      have hb : (a / 2).Coprime m' := Nat.Coprime.coprime_dvd_left (Dvd.intro_left 2 ha2.symm) hcop
      have hg : m.gcd a = 2 := by
        rw [hm, ha2, Nat.gcd_mul_left, Nat.coprime_comm.1 hb, mul_one]
      have hdm : dm m a = m' := by unfold dm; rw [hg, hm, Nat.mul_div_cancel_left m' (by norm_num)]
      rw [if_pos (by rw [hc, hdm])]
      have hE : eulerPrimes (dm m a) η'.conductor = ∅ := by
        rw [hdm, hc]
        ext ℓ; simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty,
          iff_false]
        rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
      have hT : (m.totient : ℂ) / (dm m a).totient = 1 := by
        rw [hdm, hm, Nat.totient_mul h2m', Nat.totient_two, one_mul]
        exact div_self (by exact_mod_cast (Nat.totient_pos.2 hm'0).ne')
      rw [hE, prod_empty, hT, hg, primChar_lift' hdvd η (a / 2) hb]
      ring
  · rw [if_neg hcop, if_neg]
    rw [hc]
    intro hd
    apply hcop
    have hg : m.gcd a ∣ m := Nat.gcd_dvd_left _ _
    obtain ⟨t, ht⟩ := hd
    have h1 : m = m' * t * m.gcd a := by
      unfold dm at ht; rw [← ht, Nat.div_mul_cancel hg]
    have h2 : m.gcd a * t = 2 := by
      have : m' * (m.gcd a * t) = m' * 2 := by
        rw [show m' * (m.gcd a * t) = m' * t * m.gcd a by ring, ← h1, hm]; ring
      exact Nat.eq_of_mul_eq_mul_left hm'0 this
    have hg2 : m.gcd a ∣ 2 := Dvd.intro t h2
    have hd1 : a.gcd m' ∣ m.gcd a :=
      Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_right a m') hdvd) (Nat.gcd_dvd_left a m')
    have hd2 : a.gcd m' ∣ 2 := dvd_trans hd1 hg2
    rcases (Nat.dvd_prime Nat.prime_two).1 hd2 with h | h
    · exact h
    · have : 2 ∣ m' := h ▸ Nat.gcd_dvd_right a m'
      omega
theorem psi_Phi5 {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (c1 c2 c3 z : ℂ)
    (w y y' V : ZMod N) :
    ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * Phi5 c1 c2 c3 z w y y' V (u : ZMod N) =
      c1 * ψ (2 * w) - z * c1 * ψ w + c2 * ψ y - z * c2 * ψ y' + c3 * ψ V := by
  have key : ∀ (X : ZMod N) (c : ℂ),
      ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * (if (u : ZMod N) = X then c else 0) = c * ψ X := by
    intro X c
    have := sum_indicator ψ 1 X isUnit_one
    simp only [mul_one, map_one, inv_one] at this
    rw [← this, mul_sum]
    refine sum_congr rfl (fun u _ => ?_)
    split_ifs <;> ring
  unfold Phi5
  simp only [mul_add, sum_add_distrib, key]
  ring
theorem sum3 (f : Fin 3 → ℂ) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ t, f t = f i + f j + f k := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
    | (simp [Fin.sum_univ_three]; done) | (simp [Fin.sum_univ_three]; ring)
noncomputable def cT (p m' : ℕ) (η : DirichletCharacter ℂ m') (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (t : Fin 3) : ℂ :=
  if ¬ p ∣ a t ∧ (a t).Coprime m' then
    (e t : ℂ) * (if a t % 2 = 1 then η (a t : ZMod m') else η ((a t / 2 : ℕ) : ZMod m'))
  else 0
theorem two_mul_half (hp7 : 7 ≤ p) : (2 : ZMod (p ^ r)) * (2 : ZMod (p ^ r))⁻¹ = 1 := by
  have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
  rw [Nat.cast_ofNat] at this
  exact ZMod.mul_inv_of_unit _ this
theorem top_formula (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)} (hψ : ψ.IsPrimitive)
    {η : DirichletCharacter ℂ m'} (hη : η.IsPrimitive) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0) :
    ∑ t, (e t : ℂ) * bracket (chi ψ (changeLevel hdvd η)) (a t) =
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) *
        Phi5 (cT p m' η a e i) (cT p m' η a e j) (cT p m' η a e k) (η 2)⁻¹
          ((2 : ZMod (p ^ r))⁻¹ * a i) (a j) ((2 : ZMod (p ^ r))⁻¹ * a j)
          ((a k / 2 : ℕ) : ZMod (p ^ r)) (u : ZMod (p ^ r)) := by
  rw [psi_Phi5, sum3 _ i j k hij hik hjk]
  set h := (2 : ZMod (p ^ r))⁻¹
  have hh := two_mul_half (r := r) hp7
  have hψh : ψ h = ψ⁻¹ 2 := by
    rw [MulChar.inv_apply_eq_inv']
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, mul_comm, hh, map_one]
  have h2 : ∀ x : ZMod (p ^ r), 2 * (h * x) = x := fun x => by rw [← mul_assoc, hh, one_mul]
  have hodd_t : ∀ t, a t % 2 = 1 → (e t : ℂ) * bracket (chi ψ (changeLevel hdvd η)) (a t) =
      cT p m' η a e t * ψ (2 * (h * a t)) - (η 2)⁻¹ * cT p m' η a e t * ψ (h * a t) := by
    intro t ht
    unfold cT
    by_cases hpa : p ∣ a t
    · rw [bracket_p_dvd hr hpm hψ _ _ hpa, if_neg (fun h' => h'.1 hpa)]; ring
    rw [top_term hpm hm hodd hdvd hψ hη _ hpa, h2, map_mul, hψh]
    simp only [ht, hpa, not_false_eq_true, true_and, ↓reduceIte]
    split_ifs <;> first | ring | (exfalso; contradiction)
  have heven : (e k : ℂ) * bracket (chi ψ (changeLevel hdvd η)) (a k) =
      cT p m' η a e k * ψ ((a k / 2 : ℕ) : ZMod (p ^ r)) := by
    unfold cT
    by_cases hpa : p ∣ a k
    · rw [bracket_p_dvd hr hpm hψ _ _ hpa, if_neg (fun h' => h'.1 hpa)]; ring
    rw [top_term hpm hm hodd hdvd hψ hη _ hpa]
    simp only [hk, hpa, not_false_eq_true, true_and, zero_ne_one, ↓reduceIte]
    split_ifs <;> first | ring | (exfalso; contradiction)
  rw [hodd_t i hi, hodd_t j hj, heven, h2, h2]
  ring
theorem top_vanish (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) {η : DirichletCharacter ℂ m'} (hη : η.IsPrimitive)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0) :
    ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = -η (-1) →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) *
        Phi5 (cT p m' η a e i) (cT p m' η a e j) (cT p m' η a e k) (η 2)⁻¹
          ((2 : ZMod (p ^ r))⁻¹ * a i) (a j) ((2 : ZMod (p ^ r))⁻¹ * a j)
          ((a k / 2 : ℕ) : ZMod (p ^ r)) (u : ZMod (p ^ r)) = 0 := by
  intro ψ hψ hψε
  rw [← top_formula hp7 hr hpm hm hodd hdvd hψ hη a e i j k hij hik hjk hi hj hk]
  have hη2 : η (-1) * η (-1) = 1 := by
    rcases η.even_or_odd with h | h
    · rw [show η (-1) = 1 from h]; ring
    · rw [show η (-1) = -1 from h]; ring
  have hodd' : (chi ψ (changeLevel hdvd η)).Odd := by
    show (chi ψ (changeLevel hdvd η)) (-1) = -1
    rw [MulChar.coeToFun_mul, Pi.mul_apply,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) (changeLevel hdvd η),
      Erdos634.LemmaSG2.changeLevel_neg_one hdvd η, hψε]
    linear_combination -hη2
  exact hP _ hodd' (by rw [conductor_chi hpm hψ]; exact Nat.dvd_mul_right _ _)
end Top
theorem cast_p_of_unitsMap {p r : ℕ} [hp : Fact p.Prime] (hr : 2 ≤ r) (v w : (ZMod (p ^ r))ˣ)
    (h : ZMod.unitsMap (pred_dvd p r) v = ZMod.unitsMap (pred_dvd p r) w) :
    ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) (v : ZMod (p ^ r)) =
      ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) (w : ZMod (p ^ r)) := by
  have h1 := congrArg Units.val h
  rw [ZMod.unitsMap_val, ZMod.unitsMap_val] at h1
  have hp1 : p ∣ p ^ (r - 1) := dvd_pow_self p (by omega)
  have hc := ZMod.castHom_comp hp1 (pred_dvd p r)
  have e1 := RingHom.congr_fun hc (v : ZMod (p ^ r))
  have e2 := RingHom.congr_fun hc (w : ZMod (p ^ r))
  simp only [RingHom.comp_apply, ZMod.castHom_apply] at e1 e2
  simp only [ZMod.castHom_apply]
  rw [← e1, ← e2, h1]
theorem lemmaN_groups {p r : ℕ} [hp : Fact p.Prime] (hr : 2 ≤ r) (Φ : (ZMod (p ^ r))ˣ → ℂ)
    {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0)
    {k : ℕ} (hk : k < p) (T : Fin k → Finset (ZMod (p ^ r)))
    (hsupp : ∀ v : (ZMod (p ^ r))ˣ, Φ v ≠ 0 ∨ Φ (-v) ≠ 0 → ∃ i, (v : ZMod (p ^ r)) ∈ T i)
    (hinj : ∀ i, ∀ a ∈ T i, ∀ b ∈ T i, IsUnit a → IsUnit b →
      ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) a =
        ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) b → a = b) :
    ∀ u, Φ u = -ε * Φ (-u) := by
  classical
  refine lemmaN_a (by omega) Φ hε h (fun u => ?_)
  rw [Erdos634.LemmaSFC.card_N (by omega), if_neg (by omega)]
  refine lt_of_le_of_lt ?_ hk
  calc _ ≤ (univ.biUnion (fun i : Fin k => univ.filter (fun v : (ZMod (p ^ r))ˣ =>
          ZMod.unitsMap (pred_dvd p r) v = ZMod.unitsMap (pred_dvd p r) u ∧
            (v : ZMod (p ^ r)) ∈ T i))).card := by
        refine card_le_card (fun v hv => ?_)
        obtain ⟨-, hvu, hs⟩ := mem_filter.1 hv
        obtain ⟨i, hi⟩ := hsupp v hs
        exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, hvu, hi⟩⟩
    _ ≤ ∑ i : Fin k, 1 := by
        refine card_biUnion_le.trans (sum_le_sum (fun i _ => card_le_one.2 (fun v hv w hw => ?_)))
        obtain ⟨-, hv1, hv2⟩ := mem_filter.1 hv
        obtain ⟨-, hw1, hw2⟩ := mem_filter.1 hw
        exact Units.ext (hinj i _ hv2 _ hw2 v.isUnit w.isUnit
          (cast_p_of_unitsMap hr v w (hv1.trans hw1.symm)))
    _ = k := by simp
theorem inj_group {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : r ≠ 0) (L : List ℤ)
    (hL : ∀ a ∈ L, ∀ b ∈ L, a ≠ b →
      (a - b).natAbs ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12} : Finset ℕ)) (x : ZMod (p ^ r)) :
    ∀ a ∈ (L.map (fun k : ℤ => (k : ZMod (p ^ r)) * x)).toFinset,
    ∀ b ∈ (L.map (fun k : ℤ => (k : ZMod (p ^ r)) * x)).toFinset, IsUnit a → IsUnit b →
      ZMod.castHom (dvd_pow_self p hr) (ZMod p) a = ZMod.castHom (dvd_pow_self p hr) (ZMod p) b →
        a = b := by
  intro a ha b hb hua _ hab
  simp only [List.mem_toFinset, List.mem_map] at ha hb
  obtain ⟨k1, hk1, rfl⟩ := ha
  obtain ⟨k2, hk2, rfl⟩ := hb
  by_cases hk : k1 = k2
  · rw [hk]
  exfalso
  have hxu : IsUnit x := isUnit_of_mul_isUnit_right hua
  have hX : ZMod.castHom (dvd_pow_self p hr) (ZMod p) x ≠ 0 :=
    (hxu.map (ZMod.castHom (dvd_pow_self p hr) (ZMod p))).ne_zero
  rw [map_mul, map_mul, map_intCast, map_intCast] at hab
  have h0 : (((k1 - k2 : ℤ)) : ZMod p) = 0 := by
    have : ((k1 : ZMod p) - k2) * ZMod.castHom (dvd_pow_self p hr) (ZMod p) x = 0 := by
      rw [sub_mul, hab, sub_self]
    push_cast
    exact (mul_eq_zero.1 this).resolve_right hX
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  have hd : p ∣ (k1 - k2).natAbs := Int.natCast_dvd.1 h0
  have hmem := hL k1 hk1 k2 hk2 hk
  have hpos : 0 < (k1 - k2).natAbs := Int.natAbs_pos.2 (sub_ne_zero.2 hk)
  have hle := Nat.le_of_dvd hpos hd
  have hpr := hp.out
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h <;> rw [h] at hd hle <;>
    first
    | omega
    | (interval_cases p <;> revert hd hpr <;> decide)
theorem Phi5_supp {R : Type*} [CommRing R] [DecidableEq R] {c1 c2 c3 z : ℂ} {w y y' V u : R}
    (h : Phi5 c1 c2 c3 z w y y' V u ≠ 0) :
    (c1 ≠ 0 ∧ (u = 2 * w ∨ u = w)) ∨ (c2 ≠ 0 ∧ (u = y ∨ u = y')) ∨ (c3 ≠ 0 ∧ u = V) := by
  by_contra hno
  push Not at hno
  apply h
  unfold Phi5
  obtain ⟨h1, h2, h3⟩ := hno
  by_cases hc1 : c1 = 0
  · by_cases hc2 : c2 = 0
    · by_cases hc3 : c3 = 0
      · subst hc1 hc2 hc3; simp
      · rw [if_neg (h3 hc3)]; subst hc1 hc2; simp
    · rw [if_neg (h2 hc2).1, if_neg (h2 hc2).2]
      by_cases hc3 : c3 = 0
      · subst hc1 hc3; simp
      · rw [if_neg (h3 hc3)]; subst hc1; simp
  · rw [if_neg (h1 hc1).1, if_neg (h1 hc1).2]
    by_cases hc2 : c2 = 0
    · by_cases hc3 : c3 = 0
      · subst hc2 hc3; simp
      · rw [if_neg (h3 hc3)]; subst hc2; simp
    · rw [if_neg (h2 hc2).1, if_neg (h2 hc2).2]
      by_cases hc3 : c3 = 0
      · subst hc3; simp
      · rw [if_neg (h3 hc3)]; simp
end Erdos634.LemmaSEvenComp
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSEvenTop
open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSN (pred_dvd lemmaN_b lemmaN_c)
open Erdos634.LemmaSEvenT (Phi5 theoremT)
open Erdos634.LemmaSEvenComp
def G {N : ℕ} (x : ZMod N) (L : List ℤ) : Finset (ZMod N) :=
  (L.map (fun k : ℤ => (k : ZMod N) * x)).toFinset
theorem mem_G {N : ℕ} {x v : ZMod N} {L : List ℤ} (k : ℤ) (hk : k ∈ L)
    (hv : v = (k : ZMod N) * x) : v ∈ G x L := by
  unfold G; rw [List.mem_toFinset, List.mem_map]; exact ⟨k, hk, hv.symm⟩
noncomputable def PhiTop (p r m' : ℕ) (η : DirichletCharacter ℂ m') (a : Fin 3 → ℕ)
    (e : Fin 3 → ℚ) (i j k : Fin 3) (u : ZMod (p ^ r)) : ℂ :=
  Phi5 (cT p m' η a e i) (cT p m' η a e j) (cT p m' η a e k) (η 2)⁻¹
    ((2 : ZMod (p ^ r))⁻¹ * a i) (a j) ((2 : ZMod (p ^ r))⁻¹ * a j)
    ((a k / 2 : ℕ) : ZMod (p ^ r)) u
section
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']
theorem PhiTop_supp (hp7 : 7 ≤ p) (η : DirichletCharacter ℂ m') (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (i j k : Fin 3) (u : ZMod (p ^ r)) (h : PhiTop p r m' η a e i j k u ≠ 0) :
    u = 2 * ((2 : ZMod (p ^ r))⁻¹ * a i) ∨ u = (2 : ZMod (p ^ r))⁻¹ * a i ∨
      u = 2 * ((2 : ZMod (p ^ r))⁻¹ * a j) ∨ u = (2 : ZMod (p ^ r))⁻¹ * a j ∨
      u = ((a k / 2 : ℕ) : ZMod (p ^ r)) := by
  have hh := two_mul_half (r := r) hp7
  have hy : (a j : ZMod (p ^ r)) = 2 * ((2 : ZMod (p ^ r))⁻¹ * a j) := by
    rw [← mul_assoc, hh, one_mul]
  rcases Erdos634.LemmaSEvenComp.Phi5_supp h with ⟨-, h1 | h1⟩ | ⟨-, h1 | h1⟩ | ⟨-, h1⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl (h1.trans hy)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
theorem top_sym (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) {η : DirichletCharacter ℂ m'} (hη : η.IsPrimitive)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0)
    (hcase : 2 ≤ r ∨ (r = 1 ∧ (η.Even ∨ ∃ P : Finset (ZMod (p ^ r)),
      (∀ v : ZMod (p ^ r), IsUnit v → (PhiTop p r m' η a e i j k v ≠ 0 ∨
        PhiTop p r m' η a e i j k (-v) ≠ 0) → v ∈ P) ∧ P.card < p - 1))) :
    ∀ u : ZMod (p ^ r), IsUnit u →
      PhiTop p r m' η a e i j k u = η (-1) * PhiTop p r m' η a e i j k (-u) := by
  have hvan := top_vanish hp7 hr hpm hm hodd hdvd hη a e hP i j k hij hik hjk hi hj hk
  set Φ : (ZMod (p ^ r))ˣ → ℂ := fun v => PhiTop p r m' η a e i j k (v : ZMod (p ^ r)) with hΦ
  have hΦneg : ∀ v : (ZMod (p ^ r))ˣ, Φ (-v) = PhiTop p r m' η a e i j k (-(v : ZMod (p ^ r))) :=
    fun v => by simp only [Φ, Units.val_neg]
  have hvan' : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = -η (-1) →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0 := hvan
  intro u hu
  obtain ⟨U, rfl⟩ := hu
  rw [← hΦneg]
  change Φ U = η (-1) * Φ (-U)
  rcases hcase with hr2 | ⟨rfl, hc⟩
  · have hε : -η (-1) = 1 ∨ -η (-1) = -1 := by
      rcases η.even_or_odd with h | h
      · right; rw [show η (-1) = 1 from h]
      · left; rw [show η (-1) = -1 from h, neg_neg]
    have hh := two_mul_half (r := r) hp7
    set w := (2 : ZMod (p ^ r))⁻¹ * (a i : ZMod (p ^ r))
    set y' := (2 : ZMod (p ^ r))⁻¹ * (a j : ZMod (p ^ r))
    set V := ((a k / 2 : ℕ) : ZMod (p ^ r))
    let T : Fin 3 → Finset (ZMod (p ^ r)) :=
      ![G w [2, -2, 1, -1], G y' [2, -2, 1, -1], G V [1, -1]]
    have hsupp : ∀ v : (ZMod (p ^ r))ˣ, Φ v ≠ 0 ∨ Φ (-v) ≠ 0 → ∃ i, (v : ZMod (p ^ r)) ∈ T i := by
      intro v hv
      rcases hv with hv | hv
      · rcases PhiTop_supp hp7 η a e i j k _ hv with h1 | h1 | h1 | h1 | h1
        · exact ⟨0, mem_G 2 (by simp) (by rw [h1]; push_cast; ring)⟩
        · exact ⟨0, mem_G 1 (by simp) (by rw [h1]; push_cast; ring)⟩
        · exact ⟨1, mem_G 2 (by simp) (by rw [h1]; push_cast; ring)⟩
        · exact ⟨1, mem_G 1 (by simp) (by rw [h1]; push_cast; ring)⟩
        · exact ⟨2, mem_G 1 (by simp) (by rw [h1]; push_cast; ring)⟩
      · rw [hΦneg] at hv
        rcases PhiTop_supp hp7 η a e i j k _ hv with h1 | h1 | h1 | h1 | h1
        · exact ⟨0, mem_G (-2) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
        · exact ⟨0, mem_G (-1) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
        · exact ⟨1, mem_G (-2) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
        · exact ⟨1, mem_G (-1) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
        · exact ⟨2, mem_G (-1) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
    have hinj : ∀ i, ∀ x ∈ T i, ∀ y ∈ T i, IsUnit x → IsUnit y →
        ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) x =
          ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) y → x = y := by
      intro t
      fin_cases t
      · exact inj_group hp7 (by omega) [2, -2, 1, -1] (by decide) w
      · exact inj_group hp7 (by omega) [2, -2, 1, -1] (by decide) y'
      · exact inj_group hp7 (by omega) [1, -1] (by decide) V
    have := lemmaN_groups hr2 Φ hε hvan' (k := 3) (by omega) T hsupp hinj U
    rw [this, neg_neg]
  · rcases η.even_or_odd with hev | hod
    · have := lemmaN_b Φ (fun ψ hψ h1 => hvan' ψ hψ (by rw [h1, show η (-1) = 1 from hev])) U
      rw [this, show η (-1) = 1 from hev, one_mul]
    · rcases hc with hc | ⟨P, hPs, hPc⟩
      · exfalso
        have h1 : η (-1) = 1 := hc
        have h2 : η (-1) = -1 := hod
        rw [h1] at h2; norm_num at h2
      · have hcard : (univ.filter (fun v : (ZMod (p ^ 1))ˣ => Φ v + Φ (-v) ≠ 0)).card < p - 1 := by
          refine lt_of_le_of_lt ?_ hPc
          calc _ ≤ (univ.filter (fun v : (ZMod (p ^ 1))ˣ => (v : ZMod (p ^ 1)) ∈ P)).card := by
                refine card_le_card (fun v hv => ?_)
                have hv' := (mem_filter.1 hv).2
                refine mem_filter.2 ⟨mem_univ _, hPs _ v.isUnit ?_⟩
                by_contra hno
                push Not at hno
                apply hv'
                rw [hΦneg]; simp only [Φ, hno.1, hno.2, add_zero]
            _ ≤ P.card := by
                refine card_le_card_of_injOn (fun v => (v : ZMod (p ^ 1))) ?_ ?_
                · intro v hv; exact (mem_filter.1 hv).2
                · intro v _ w _ hvw; exact Units.ext hvw
        have := lemmaN_c Φ (fun ψ hψ h1 => hvan' ψ hψ
          (by rw [h1, show η (-1) = -1 from hod, neg_neg])) hcard U
        rw [this, show η (-1) = -1 from hod]; ring
theorem top_T (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) {η : DirichletCharacter ℂ m'} (hη : η.IsPrimitive)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hk : a k % 2 = 0)
    (hsym : ∀ u : ZMod (p ^ r), IsUnit u →
      PhiTop p r m' η a e i j k u = η (-1) * PhiTop p r m' η a e i j k (-u)) :
    cT p m' η a e k = 0 ∧
      ((cT p m' η a e i = 0 ∧ cT p m' η a e j = 0) ∨
        ((a j : ZMod (p ^ r)) = a i ∧ cT p m' η a e i + cT p m' η a e j = 0) ∨
        ((a j : ZMod (p ^ r)) = -(a i : ZMod (p ^ r)) ∧
          cT p m' η a e i = η (-1) * cT p m' η a e j)) := by
  have hh := two_mul_half (r := r) hp7
  have u2 : IsUnit (2 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have u3 : IsUnit (3 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 3) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have u5 : IsUnit (5 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 5) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have uh : IsUnit ((2 : ZMod (p ^ r))⁻¹) := IsUnit.of_mul_eq_one_right _ hh
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  have hunit : ∀ t, ¬ p ∣ a t → IsUnit ((a t : ℕ) : ZMod (p ^ r)) := fun t h =>
    (ZMod.isUnit_iff_coprime _ _).2
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h).symm)
  have hunit' : ∀ b : ℕ, ¬ p ∣ b → IsUnit ((b : ℕ) : ZMod (p ^ r)) := fun b h =>
    (ZMod.isUnit_iff_coprime _ _).2
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h).symm)
  have hcT : ∀ t, cT p m' η a e t ≠ 0 → ¬ p ∣ a t := by
    intro t h hpa; apply h; unfold cT; rw [if_neg (fun h' => h'.1 hpa)]
  have hsum3 : ((a i : ℕ) : ZMod (p ^ r)) + a j + a k = 0 := by
    have h0 : ((a 0 + a 1 + a 2 : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    push_cast at h0
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first
      | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h0 ⊢; linear_combination h0)
  set V := ((a k / 2 : ℕ) : ZMod (p ^ r)) with hV
  have h2V : (2 : ZMod (p ^ r)) * V = a k := by
    rw [hV, show (2 : ZMod (p ^ r)) = ((2 : ℕ) : ZMod (p ^ r)) by norm_num, ← Nat.cast_mul,
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)]
  have hrel : 2 * ((2 : ZMod (p ^ r))⁻¹ * a i) + a j + 2 * V = 0 := by
    rw [← mul_assoc, hh, one_mul, h2V]; exact hsum3
  have hy' : 2 * ((2 : ZMod (p ^ r))⁻¹ * a j) = a j := by rw [← mul_assoc, hh, one_mul]
  have hz : (η 2)⁻¹ ≠ 0 := by
    have hu : IsUnit (2 : ZMod m') := by
      have := (ZMod.isUnit_iff_coprime 2 m').2 (Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd))
      rwa [Nat.cast_ofNat] at this
    obtain ⟨u2', hu2'⟩ := hu
    rw [← hu2']
    exact inv_ne_zero (Erdos634.DirichletCRT.unit_val_ne_zero η u2')
  have hc1 : cT p m' η a e i ≠ 0 → IsUnit ((2 : ZMod (p ^ r))⁻¹ * a i) :=
    fun h => uh.mul (hunit i (hcT i h))
  have hc2 : cT p m' η a e j ≠ 0 → IsUnit ((2 : ZMod (p ^ r))⁻¹ * a j) :=
    fun h => uh.mul (hunit j (hcT j h))
  have hc3 : cT p m' η a e k ≠ 0 → IsUnit V := by
    intro h
    have hpk := hcT k h
    have hpk2 : ¬ p ∣ a k / 2 := fun hd => hpk (by
      rw [← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)]; exact dvd_mul_of_dvd_right hd 2)
    exact hunit' _ hpk2
  obtain ⟨h3, h⟩ := theoremT u2 u3 u5 hrel hy' hz hc1 hc2 hc3 hsym
  refine ⟨h3, ?_⟩
  rcases h with h | ⟨hy, hs⟩ | ⟨hy, hs⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by rw [hy, ← mul_assoc, hh, one_mul], hs⟩)
  · exact Or.inr (Or.inr ⟨by rw [hy, ← mul_assoc, hh, one_mul], hs⟩)
theorem sum3_zmod (a : Fin 3 → ℕ) (hsum : a 0 + a 1 + a 2 = p ^ r * m) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((a i : ℕ) : ZMod (p ^ r)) + a j + a k = 0 := by
  have h0 : ((a 0 + a 1 + a 2 : ℕ) : ZMod (p ^ r)) = 0 := by
    rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  push_cast at h0
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h0 ⊢; linear_combination h0)
theorem top_rel_all (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0)
    (hfi : ¬ p ∣ a i ∧ (a i).Coprime m') (hfj : ¬ p ∣ a j ∧ (a j).Coprime m')
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hβ : (a j : ZMod (p ^ r)) = (σ : ZMod (p ^ r)) * a i) :
    ∀ η : DirichletCharacter ℂ m', η.IsPrimitive →
      ((e i : ℚ) : ℂ) * η (a i : ZMod m') + (σ : ℂ) * (e j : ℚ) * η (((σ * a j : ℤ)) : ZMod m') = 0 := by
  intro η hη
  have hh := two_mul_half (r := r) hp7
  have hh' : (2 : ZMod (p ^ r))⁻¹ * 2 = 1 := by rw [mul_comm]; exact hh
  have u2 : IsUnit (2 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  have hui : IsUnit ((a i : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime _ _).2
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hfi.1).symm)
  set w := (2 : ZMod (p ^ r))⁻¹ * (a i : ZMod (p ^ r)) with hw
  have hwu : IsUnit w := (IsUnit.of_mul_eq_one_right _ hh).mul hui
  have hai : (a i : ZMod (p ^ r)) = 2 * w := by rw [hw, ← mul_assoc, hh, one_mul]
  have hy' : (2 : ZMod (p ^ r))⁻¹ * a j = (σ : ZMod (p ^ r)) * w := by
    rw [hβ, hai, hw]; linear_combination ((σ : ZMod (p ^ r)) * (2 : ZMod (p ^ r))⁻¹ * a i) * hh'
  have h3 := sum3_zmod (m := m) a hsum i j k hij hik hjk
  have hV : ((a k / 2 : ℕ) : ZMod (p ^ r)) = -(1 + (σ : ZMod (p ^ r))) * w := by
    apply u2.mul_left_cancel
    have h2V : (2 : ZMod (p ^ r)) * ((a k / 2 : ℕ) : ZMod (p ^ r)) = a k := by
      rw [show (2 : ZMod (p ^ r)) = ((2 : ℕ) : ZMod (p ^ r)) by norm_num, ← Nat.cast_mul,
        Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)]
    rw [h2V]
    have : (a j : ZMod (p ^ r)) = σ * (2 * w) := by rw [hβ, hai]
    linear_combination h3 - hai - this
  set P : Finset (ZMod (p ^ r)) := {2 * w, -(2 * w), w, -w} with hPdef
  have hPc : P.card < p - 1 := lt_of_le_of_lt Finset.card_le_four (by omega)
  have hPs : ∀ v : ZMod (p ^ r), IsUnit v → (PhiTop p r m' η a e i j k v ≠ 0 ∨
      PhiTop p r m' η a e i j k (-v) ≠ 0) → v ∈ P := by
    intro v hv hne
    have key : ∀ t : ZMod (p ^ r), IsUnit t → PhiTop p r m' η a e i j k t ≠ 0 →
        t = 2 * w ∨ t = w ∨ t = -(2 * w) ∨ t = -w := by
      intro t ht hne'
      rcases PhiTop_supp hp7 η a e i j k t hne' with h1 | h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · rw [hy'] at h1
        rcases hσ with rfl | rfl
        · left; rw [h1]; push_cast; ring
        · right; right; left; rw [h1]; push_cast; ring
      · rw [hy'] at h1
        rcases hσ with rfl | rfl
        · right; left; rw [h1]; push_cast; ring
        · right; right; right; rw [h1]; push_cast; ring
      · rw [hV] at h1
        rcases hσ with rfl | rfl
        · right; right; left; rw [h1]; push_cast; ring
        · exfalso; rw [h1] at ht; push_cast at ht; simp at ht
    rcases hne with h | h
    · rcases key v hv h with h1 | h1 | h1 | h1 <;> rw [h1] <;> simp [P]
    · rcases key (-v) hv.neg h with h1 | h1 | h1 | h1
      · rw [← neg_neg v, h1]; simp [P]
      · rw [← neg_neg v, h1]; simp [P]
      · rw [← neg_neg v, h1, neg_neg]; simp [P]
      · rw [← neg_neg v, h1, neg_neg]; simp [P]
  have hsym := top_sym hp7 hr hpm hm hodd hdvd hη a e hP i j k hij hik hjk hi hj hk
    (by rcases Nat.lt_or_ge r 2 with h | h
        · exact Or.inr ⟨by omega, Or.inr ⟨P, hPs, hPc⟩⟩
        · exact Or.inl h)
  obtain ⟨-, h⟩ := top_T hp7 hr hpm hm hodd hdvd hη a e hsum i j k hij hik hjk hk hsym
  have hci : cT p m' η a e i = (e i : ℂ) * η (a i : ZMod m') := by
    unfold cT; rw [if_pos hfi, if_pos hi]
  have hcj : cT p m' η a e j = (e j : ℂ) * η (a j : ZMod m') := by
    unfold cT; rw [if_pos hfj, if_pos hj]
  have hne2 : (a i : ZMod (p ^ r)) ≠ -(a i : ZMod (p ^ r)) := by
    intro h0
    have : (2 : ZMod (p ^ r)) * a i = 0 := by linear_combination h0
    exact (u2.mul hui).ne_zero this
  rw [hci, hcj] at h
  rcases hσ with rfl | rfl
  · have hβ' : (a j : ZMod (p ^ r)) = a i := by rw [hβ]; push_cast; ring
    rcases h with ⟨h1, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩
    · push_cast; rw [one_mul, one_mul]; linear_combination h1 + h2
    · push_cast; rw [one_mul, one_mul]; linear_combination h2
    · exact absurd (hβ'.symm.trans h1) hne2
  · have hβ' : (a j : ZMod (p ^ r)) = -(a i) := by rw [hβ]; push_cast; ring
    have hneg : η ((((-1 : ℤ) * a j : ℤ)) : ZMod m') = η (-1) * η (a j : ZMod m') := by
      rw [← map_mul]; congr 1; push_cast; ring
    rw [hneg]
    rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · push_cast; linear_combination h1 - η (-1) * h2
    · exact absurd (h1.symm.trans hβ') hne2
    · push_cast; linear_combination h2
end
end Erdos634.LemmaSEvenTop
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSG2Avoid
open Erdos634.LemmaSN (pred_dvd isPrimitive_iff_not_factorsThrough)
theorem card_mul_card_triv {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) [DecidablePred (· ∈ H)] :
    Fintype.card H *
      (univ.filter (fun χ : DirichletCharacter ℂ n => ∀ h ∈ H, χ (h : ZMod n) = 1)).card
      = n.totient := by
  classical
  set K := univ.filter (fun χ : DirichletCharacter ℂ n => ∀ h ∈ H, χ (h : ZMod n) = 1) with hK
  have hsum : ∀ χ : DirichletCharacter ℂ n, ∑ h : H, χ ((h : (ZMod n)ˣ) : ZMod n)
      = if χ ∈ K then (Fintype.card H : ℂ) else 0 := by
    intro χ
    split_ifs with hχ
    · have hK' := (mem_filter.1 hχ).2
      rw [sum_congr rfl (fun h _ => hK' h.1 h.property), sum_const, card_univ, nsmul_eq_mul, mul_one]
    · simp only [hK, mem_filter, mem_univ, true_and, not_forall] at hχ
      obtain ⟨h0, hh0, hne⟩ := hχ
      set S := ∑ h : H, χ ((h : (ZMod n)ˣ) : ZMod n) with hS
      have hSS : S = χ (h0 : ZMod n) * S := by
        rw [hS]
        conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft (⟨h0, hh0⟩ : H))]
        rw [mul_sum]
        refine sum_congr rfl (fun h _ => ?_)
        simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Units.val_mul, map_mul]
      have : (1 - χ (h0 : ZMod n)) * S = 0 := by rw [sub_mul, one_mul, ← hSS, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have htot : ∑ χ : DirichletCharacter ℂ n, ∑ h : H, χ ((h : (ZMod n)ˣ) : ZMod n)
      = (n.totient : ℂ) := by
    rw [sum_comm]
    simp_rw [DirichletCharacter.sum_characters_eq ℂ]
    rw [sum_eq_single (1 : H)]
    · simp
    · intro h _ hne
      rw [if_neg]
      intro h1
      exact hne (Subtype.ext (Units.ext (by simpa using h1)))
    · intro h; exact absurd (mem_univ _) h
  simp_rw [hsum] at htot
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul] at htot
  have : ((Fintype.card H * K.card : ℕ) : ℂ) = (n.totient : ℂ) := by push_cast; rw [← htot]; ring
  exact_mod_cast this
theorem not_dvd_small {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hr : 1 ≤ r) (d : ℤ) (hd0 : d ≠ 0)
    (hdb : d.natAbs ≤ 18) (h7 : ¬ (7 : ℤ) ∣ d) (h11 : ¬ (11 : ℤ) ∣ d) (h13 : ¬ (13 : ℤ) ∣ d)
    (h17 : ¬ (17 : ℤ) ∣ d) : ¬ ((p ^ r : ℕ) : ℤ) ∣ d := by
  intro h
  have hpd : (p : ℤ) ∣ d :=
    dvd_trans (by exact_mod_cast dvd_pow_self p (by omega : r ≠ 0)) h
  have hle : p ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hd0) (Int.natCast_dvd.1 hpd)
  have hp18 : p ≤ 18 := le_trans hle hdb
  interval_cases p <;> first | exact h7 (by exact_mod_cast hpd) | exact h11 (by exact_mod_cast hpd) | exact h13 (by exact_mod_cast hpd) | exact h17 (by exact_mod_cast hpd) | (exfalso; norm_num at hp)
theorem six_le_card {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) (c : ℤ)
    (hc : c = 2 ∨ c = 3) (u : (ZMod (p ^ r))ˣ) (hu : (u : ZMod (p ^ r)) = (c : ZMod (p ^ r)))
    (H : Subgroup (ZMod (p ^ r))ˣ) [DecidablePred (· ∈ H)] (huH : u ∈ H) (hmH : (-1 : (ZMod (p ^ r))ˣ) ∈ H) :
    6 ≤ Fintype.card H := by
  classical
  set L : List (ZMod (p ^ r))ˣ := [1, u, u * u, -1, -u, -(u * u)] with hL
  have hvals : L.map (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)))
      = ([1, c, c * c, -1, -c, -(c * c)] : List ℤ).map (fun z : ℤ => (z : ZMod (p ^ r))) := by
    simp [hL, hu]
  have hinj : ∀ x ∈ ([1, c, c * c, -1, -c, -(c * c)] : List ℤ),
      ∀ y ∈ ([1, c, c * c, -1, -c, -(c * c)] : List ℤ),
      (x : ZMod (p ^ r)) = (y : ZMod (p ^ r)) → x = y := by
    intro x hx y hy hxy
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy
    by_contra hne
    have hd0 : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hc with rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact hne rfl
      | exact not_dvd_small hp.out hp7 hr _ hd0 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) hxy
  have hndZ : ([1, c, c * c, -1, -c, -(c * c)] : List ℤ).Nodup := by
    rcases hc with rfl | rfl <;> decide
  have hnd : L.Nodup := by
    have h1 := List.Nodup.map_on hinj hndZ
    have h2 : (L.map (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)))).Nodup := by
      rw [hvals]; exact h1
    exact List.Nodup.of_map _ h2
  have hsub : L.toFinset ⊆ univ.filter (· ∈ H) := by
    intro v hv
    rw [List.mem_toFinset] at hv
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hmu : -u ∈ H := by rw [← neg_one_mul]; exact H.mul_mem hmH huH
    have hmuu : -(u * u) ∈ H := by rw [← neg_one_mul]; exact H.mul_mem hmH (H.mul_mem huH huH)
    simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact huH
    · exact H.mul_mem huH huH
    · exact hmH
    · exact hmu
    · exact hmuu
  have := card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  rw [Fintype.card_subtype]
  simpa [hL] using this
theorem coprime_small {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (c : ℕ) (hc : c = 2 ∨ c = 3) :
    c.Coprime (p ^ r) := by
  apply Nat.Coprime.pow_right
  rcases hc with rfl | rfl
  · exact (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  · exact (Nat.coprime_primes Nat.prime_three hp).2 (by omega)
theorem card_fixed_le {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) (c : ℕ)
    (hc : c = 2 ∨ c = 3) (S : Finset (DirichletCharacter ℂ (p ^ r))) (z : ℂ)
    (hS : ∀ ψ ∈ S, ψ (-1) = -1 ∧ ψ (c : ZMod (p ^ r)) = z) :
    6 * S.card ≤ (p ^ r).totient := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rcases S.eq_empty_or_nonempty with h | ⟨ψ0, hψ0⟩
  · rw [h]; simp
  set u : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime c (coprime_small hp.out hp7 c hc) with hu
  have hucoe : (u : ZMod (p ^ r)) = (c : ZMod (p ^ r)) := ZMod.coe_unitOfCoprime _ _
  set H := Subgroup.closure ({u, -1} : Set (ZMod (p ^ r))ˣ) with hH
  have huH : u ∈ H := Subgroup.subset_closure (by simp)
  have hmH : (-1 : (ZMod (p ^ r))ˣ) ∈ H := Subgroup.subset_closure (by simp)
  have h6 : 6 ≤ Fintype.card H := by
    refine six_le_card hp7 hr (c : ℤ) (by rcases hc with rfl | rfl <;> simp) u
      (by rw [hucoe]; simp) H huH hmH
  set K := univ.filter (fun χ : DirichletCharacter ℂ (p ^ r) => ∀ h ∈ H, χ (h : ZMod (p ^ r)) = 1)
  have hHK := card_mul_card_triv H
  have hSK : S.card ≤ K.card := by
    refine card_le_card_of_injOn (fun ψ => ψ * ψ0⁻¹) ?_ ?_
    · intro ψ hψ
      rw [Finset.mem_coe, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      intro h hh
      have hle : H ≤ (ψ * ψ0⁻¹).toUnitHom.ker := by
        rw [hH, Subgroup.closure_le]
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rw [SetLike.mem_coe, MonoidHom.mem_ker]
        apply Units.ext
        rw [MulChar.coe_toUnitHom, Units.val_one]
        obtain ⟨h1, h2⟩ := hS ψ hψ
        obtain ⟨h1', h2'⟩ := hS ψ0 hψ0
        have hz : z ≠ 0 := by
          rw [← h2', ← hucoe]
          intro h0
          have := ψ0.unit_norm_eq_one u
          rw [h0, norm_zero] at this
          exact zero_ne_one this
        rcases hv with rfl | rfl
        · show ψ (u : ZMod (p ^ r)) * ψ0⁻¹ (u : ZMod (p ^ r)) = 1
          rw [MulChar.inv_apply_eq_inv', hucoe, h2, h2', mul_inv_cancel₀ hz]
        · show ψ ((-1 : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) * ψ0⁻¹ ((-1 : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) = 1
          rw [MulChar.inv_apply_eq_inv', Units.val_neg, Units.val_one, h1, h1']; norm_num
      have := hle hh
      rw [MonoidHom.mem_ker] at this
      have := congrArg Units.val this
      rwa [MulChar.coe_toUnitHom, Units.val_one] at this
    · intro x _ y _ hxy
      exact mul_right_cancel hxy
  have : 6 * K.card ≤ (p ^ r).totient := by rw [← hHK]; exact Nat.mul_le_mul_right _ h6
  omega
theorem changeLevel_neg_one' {m n : ℕ} [NeZero n] (h : m ∣ n) (ψ : DirichletCharacter ℂ m) :
    DirichletCharacter.changeLevel h ψ (-1) = ψ (-1) := by
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ h (-1)
  simp only [Units.val_neg, Units.val_one] at h1
  rw [h1, ZMod.cast_neg h, ZMod.cast_one h]
open Classical in
theorem card_odd_prim_lower {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) :
    (p ^ r).totient ≤
      2 * ((univ.filter (fun ψ : DirichletCharacter ℂ (p ^ r) => ψ (-1) = -1)).filter
        (fun ψ => ψ.IsPrimitive)).card + (p ^ (r - 1)).totient := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (p ^ (r - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hq7 : 7 ≤ p ^ r := le_trans hp7 (Nat.le_self_pow (by omega) p)
  haveI : Fact (2 < p ^ r) := ⟨by omega⟩
  have hm1 : (-1 : ZMod (p ^ r)) ≠ 1 := ZMod.neg_one_ne_one
  have hd := pred_dvd p r
  set X := univ.filter (fun ψ : DirichletCharacter ℂ (p ^ r) => ψ (-1) = -1) with hX
  set X' := univ.filter (fun ψ : DirichletCharacter ℂ (p ^ (r - 1)) => ψ (-1) = -1) with hX'
  have hP := Erdos634.LemmaSG.parity_sum (-1) (Or.inr rfl) (1 : ZMod (p ^ r))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl,
    if_neg hm1, mul_zero, add_zero, ← hX] at hP
  simp only [MulChar.map_one, mul_one, sum_const, nsmul_eq_mul] at hP
  have hXc : 2 * X.card = (p ^ r).totient := by
    have : ((2 * X.card : ℕ) : ℂ) = ((p ^ r).totient : ℂ) := by push_cast; rw [← hP]; ring
    exact_mod_cast this
  have hP' := Erdos634.LemmaSG.parity_sum (-1) (Or.inr rfl) (1 : ZMod (p ^ (r - 1)))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl,
    ← hX'] at hP'
  simp only [MulChar.map_one, mul_one, sum_const, nsmul_eq_mul] at hP'
  have hX'c : 2 * X'.card ≤ (p ^ (r - 1)).totient := by
    by_cases h1 : (-1 : ZMod (p ^ (r - 1))) = 1
    · rw [if_pos h1] at hP'
      have : ((2 * X'.card : ℕ) : ℂ) = 0 := by push_cast; linear_combination hP'
      have : 2 * X'.card = 0 := by exact_mod_cast this
      omega
    · rw [if_neg h1, mul_zero, add_zero] at hP'
      have : ((2 * X'.card : ℕ) : ℂ) = ((p ^ (r - 1)).totient : ℂ) := by
        push_cast; linear_combination hP'
      have : 2 * X'.card = (p ^ (r - 1)).totient := by exact_mod_cast this
      omega
  have hsub : X.filter (fun ψ => ¬ ψ.IsPrimitive) ⊆ X'.image (DirichletCharacter.changeLevel hd) := by
    intro ψ hψ
    obtain ⟨hψX, hnp⟩ := mem_filter.1 hψ
    have hpar := (mem_filter.1 hψX).2
    have hf : ψ.FactorsThrough (p ^ (r - 1)) :=
      not_not.1 (fun h' => hnp ((isPrimitive_iff_not_factorsThrough hr ψ).2 h'))
    have heq := hf.eq_changeLevel
    rw [mem_image]
    refine ⟨hf.χ₀, mem_filter.2 ⟨mem_univ _, ?_⟩, heq.symm⟩
    rw [← changeLevel_neg_one' hd, ← heq]; exact hpar
  have hc1 := card_le_card hsub
  have hc2 := card_image_le (s := X') (f := DirichletCharacter.changeLevel hd)
  have hsplit := card_filter_add_card_filter_not (s := X) (fun ψ => ψ.IsPrimitive)
  omega
theorem totient_pred_le {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    (p - 1) * (p ^ (r - 1)).totient ≤ (p ^ r).totient := by
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    simp [Nat.totient_prime hp]
  · have htot : (p ^ r).totient = p * (p ^ (r - 1)).totient := by
      rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]
      exact Nat.totient_mul_of_prime_of_dvd hp (dvd_pow_self p (by omega))
    rw [htot]
    exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
theorem lemmaG2 {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) (a b : ℂ)
    (_ha : a ≠ 0) (_hb : b ≠ 0) :
    ∃ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive ∧ ψ.Odd ∧
      ψ (2 : ZMod (p ^ r)) ≠ a ∧ ψ (3 : ZMod (p ^ r)) ≠ b := by
  classical
  set O := (univ.filter (fun ψ : DirichletCharacter ℂ (p ^ r) => ψ (-1) = -1)).filter
    (fun ψ => ψ.IsPrimitive) with hO
  set B2 := O.filter (fun ψ => ψ (2 : ZMod (p ^ r)) = a) with hB2
  set B3 := O.filter (fun ψ => ψ (3 : ZMod (p ^ r)) = b) with hB3
  have hmemO : ∀ ψ ∈ O, ψ (-1) = -1 ∧ ψ.IsPrimitive := by
    intro ψ hψ
    obtain ⟨h1, h2⟩ := mem_filter.1 hψ
    exact ⟨(mem_filter.1 h1).2, h2⟩
  have h2 : 6 * B2.card ≤ (p ^ r).totient := by
    refine card_fixed_le hp7 hr 2 (Or.inl rfl) B2 a (fun ψ hψ => ?_)
    obtain ⟨hψO, hψa⟩ := mem_filter.1 hψ
    exact ⟨(hmemO ψ hψO).1, by simpa using hψa⟩
  have h3 : 6 * B3.card ≤ (p ^ r).totient := by
    refine card_fixed_le hp7 hr 3 (Or.inr rfl) B3 b (fun ψ hψ => ?_)
    obtain ⟨hψO, hψb⟩ := mem_filter.1 hψ
    exact ⟨(hmemO ψ hψO).1, by simpa using hψb⟩
  have hlow := card_odd_prim_lower (p := p) hp7 hr
  rw [← hO] at hlow
  have hpred := totient_pred_le hp.out hr
  have hφ : 0 < (p ^ r).totient := Nat.totient_pos.2 (pow_pos hp.out.pos r)
  have hlt : (B2 ∪ B3).card < O.card := by
    refine lt_of_le_of_lt (card_union_le B2 B3) ?_
    by_contra hge
    push Not at hge
    have h4 : (p ^ r).totient ≤ 3 * (p ^ (r - 1)).totient := by omega
    have h5 : (p - 1) * (p ^ r).totient ≤ 3 * (p ^ r).totient := by
      calc (p - 1) * (p ^ r).totient ≤ (p - 1) * (3 * (p ^ (r - 1)).totient) :=
            Nat.mul_le_mul_left _ h4
        _ = 3 * ((p - 1) * (p ^ (r - 1)).totient) := by ring
        _ ≤ 3 * (p ^ r).totient := Nat.mul_le_mul_left _ hpred
    have := Nat.le_of_mul_le_mul_right h5 hφ
    omega
  obtain ⟨ψ, hψO, hψn⟩ := exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hodd, hprim⟩ := hmemO ψ hψO
  refine ⟨ψ, hprim, hodd, fun h => hψn (mem_union_left _ (mem_filter.2 ⟨hψO, h⟩)),
    fun h => hψn (mem_union_right _ (mem_filter.2 ⟨hψO, h⟩))⟩
end Erdos634.LemmaSG2Avoid
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSEvenD
open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit sum_indicator)
open Erdos634.LemmaSN (pred_dvd lemmaN_b)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive)
open Erdos634.LemmaSGprime (Sp tau)
open Erdos634.LemmaSEvenT (nek small_units)
open Erdos634.LemmaSEvenComp
open Erdos634.LemmaSEvenTop
theorem sp_odd {d : ℕ} (hd0 : d ≠ 0) (hd : d % 2 = 1) {z : ℤ} (hSp : Sp d z)
    (hz1 : ¬ z ≡ 1 [ZMOD d]) :
    d.factorization 3 = 1 ∧ z ≡ -1 [ZMOD 3] ∧ z ≡ 1 [ZMOD ((d / 3 : ℕ) : ℤ)] ∧ tau d z = 1 := by
  classical
  obtain ⟨q, hq, hbad⟩ : ∃ q ∈ d.primeFactors, ¬ z ≡ 1 [ZMOD (q : ℤ) ^ d.factorization q] := by
    by_contra hno; push Not at hno
    exact hz1 (Erdos634.LemmaSR1p.modEq_of_components hd0 hno)
  have h2d : ¬ 2 ∣ d := by omega
  obtain ⟨rfl, hv3, hz3⟩ : q = 3 ∧ d.factorization 3 = 1 ∧ z ≡ -1 [ZMOD 3] := by
    rcases hSp q hq with h | ⟨h1, h2, h3⟩ | ⟨h1, -, -⟩
    · exact absurd h hbad
    · subst h1; exact ⟨rfl, h2, h3⟩
    · subst h1; exact absurd (Nat.dvd_of_mem_primeFactors hq) h2d
  refine ⟨hv3, hz3, ?_, ?_⟩
  · have hd3 : d / 3 = d / 3 ^ d.factorization 3 := by rw [hv3, pow_one]
    rw [hd3]
    have hm'0 : d / 3 ^ d.factorization 3 ≠ 0 := (Nat.ordCompl_pos 3 hd0).ne'
    have hm'm : d / 3 ^ d.factorization 3 ∣ d := Nat.ordCompl_dvd d 3
    refine Erdos634.LemmaSR1p.modEq_of_components hm'0 (fun ℓ hℓ => ?_)
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have hℓm : ℓ ∈ d.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hℓp, dvd_trans (Nat.dvd_of_mem_primeFactors hℓ) hm'm, hd0⟩
    have hℓ3 : ℓ ≠ 3 := by
      rintro rfl; exact Nat.not_dvd_ordCompl Nat.prime_three hd0 (Nat.dvd_of_mem_primeFactors hℓ)
    have hfac : (d / 3 ^ d.factorization 3).factorization ℓ = d.factorization ℓ := by
      simp only [Nat.factorization_ordCompl, Finsupp.erase_ne hℓ3]
    rw [hfac]
    rcases hSp ℓ hℓm with h | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
    · exact h
    · exact absurd h1 hℓ3
    · subst h1; exact absurd (Nat.dvd_of_mem_primeFactors hℓm) h2d
  · unfold tau
    rw [card_eq_one]
    refine ⟨3, ?_⟩
    ext q'
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hq', hb⟩
      rcases hSp q' hq' with h | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
      · exact absurd h hb
      · exact h1
      · subst h1; exact absurd (Nat.dvd_of_mem_primeFactors hq') h2d
    · rintro rfl; exact ⟨hq, hbad⟩
theorem zrep {d : ℕ} [NeZero d] (x y : ℕ) (hy : y.Coprime d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ z : ℤ, z * (σ * y) ≡ x [ZMOD d] := by
  set u : ZMod d := ((σ * y : ℤ) : ZMod d) with hu_def
  have hu : IsUnit u := by
    have hy' := (ZMod.isUnit_iff_coprime y d).2 hy
    rcases hσ with rfl | rfl
    · rw [hu_def]; push_cast; rw [one_mul]; exact hy'
    · rw [hu_def]; push_cast; rw [neg_one_mul]; exact hy'.neg
  refine ⟨(((x : ZMod d) * u⁻¹).val : ℤ), ?_⟩
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    ← hu_def, Int.cast_natCast, mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]
section D
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']
theorem descent_term (hpm : ¬ p ∣ m) (hm : m = 2 * m') (hodd : m' % 2 = 1) {f : ℕ} [NeZero f]
    (hmf : m' = 3 * f) (h3f : ¬ 3 ∣ f) (hdvd : f ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)}
    (hψ : ψ.IsPrimitive) {η : DirichletCharacter ℂ f} (hη : η.IsPrimitive) (a : ℕ)
    (hpa : ¬ p ∣ a) (ha : a % 2 = 1) (hcop : a.Coprime m') :
    bracket (chi ψ (changeLevel hdvd η)) a = ψ (a : ZMod (p ^ r)) * η (a : ZMod f) *
      (1 - ψ⁻¹ 2 * (η 2)⁻¹) * (1 - ψ⁻¹ 3 * (η 3)⁻¹) := by
  set η' := changeLevel hdvd η
  have hc : η'.conductor = f := conductor_changeLevel_of_isPrimitive hdvd hη
  rw [bracket_unit hpm hψ η' a hpa]
  have hfodd : f % 2 = 1 := by omega
  have h2f : (2 : ℕ).Coprime f := Nat.coprime_two_left.2 (Nat.odd_iff.2 hfodd)
  have h3f' : (3 : ℕ).Coprime f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f
  have haf : a.Coprime f := hcop.coprime_dvd_right (Dvd.intro_left 3 hmf.symm)
  have hg : m.gcd a = 1 := by
    rw [hm, Nat.gcd_comm]
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 (Nat.odd_iff.2 ha)) hcop
  have hdm : dm m a = m := by simp [dm, hg]
  rw [if_pos (by rw [hc, hdm]; exact hdvd)]
  have hE : eulerPrimes (dm m a) η'.conductor = {2, 3} := by
    rw [hdm, hc]
    ext ℓ; simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hl, hlm, -⟩, hlf⟩
      rw [hm, hmf] at hlm
      rcases (Nat.Prime.dvd_mul hl).1 hlm with h2 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h2)
      · rcases (Nat.Prime.dvd_mul hl).1 h2 with h3 | h3
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).1 h3)
        · exact absurd h3 hlf
    · rintro (rfl | rfl)
      · exact ⟨⟨Nat.prime_two, by rw [hm]; exact dvd_mul_right 2 m', NeZero.ne m⟩,
          fun h => by omega⟩
      · exact ⟨⟨Nat.prime_three, by rw [hm, hmf]; exact Dvd.intro_left (2 * f) (by ring),
          NeZero.ne m⟩, h3f⟩
  have hT : (m.totient : ℂ) / (dm m a).totient = 1 := by
    rw [hdm]; exact div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
  rw [hE, prod_insert (by decide), prod_singleton, hT, hg, Nat.div_one,
    primChar_lift' hdvd η a haf]
  simp only [MulChar.inv_apply_eq_inv']
  rw [primChar_lift' hdvd η 2 h2f, primChar_lift' hdvd η 3 h3f']
  simp only [Nat.cast_ofNat]
  ring
theorem descent_term_six (hpm : ¬ p ∣ m) (hm : m = 2 * m') (hodd : m' % 2 = 1) {f : ℕ} [NeZero f]
    (hmf : m' = 3 * f) (h3f : ¬ 3 ∣ f) (hdvd : f ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)}
    (hψ : ψ.IsPrimitive) {η : DirichletCharacter ℂ f} (hη : η.IsPrimitive) (v : ℕ)
    (hpv : ¬ p ∣ v) (hg : m.gcd v = 6) :
    bracket (chi ψ (changeLevel hdvd η)) v =
      2 * (ψ ((v / 6 : ℕ) : ZMod (p ^ r)) * η ((v / 6 : ℕ) : ZMod f)) := by
  set η' := changeLevel hdvd η
  have hc : η'.conductor = f := conductor_changeLevel_of_isPrimitive hdvd hη
  rw [bracket_unit hpm hψ η' v hpv]
  have hm6 : m = 6 * f := by rw [hm, hmf]; ring
  have hf0 : 0 < f := Nat.pos_of_ne_zero (NeZero.ne f)
  have hfodd : f % 2 = 1 := by omega
  have h6f : (6 : ℕ).Coprime f := by
    have h2f : (2 : ℕ).Coprime f := Nat.coprime_two_left.2 (Nat.odd_iff.2 hfodd)
    have h3f' : (3 : ℕ).Coprime f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f
    exact Nat.Coprime.mul_left h2f h3f'
  have hdm : dm m v = f := by
    unfold dm; rw [hg, hm6, Nat.mul_div_cancel_left f (by norm_num)]
  rw [if_pos (by rw [hc, hdm])]
  have hE : eulerPrimes (dm m v) η'.conductor = ∅ := by
    rw [hdm, hc]
    ext ℓ; simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
    rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
  have hT : (m.totient : ℂ) / (dm m v).totient = 2 := by
    rw [hdm, hm6, Nat.totient_mul h6f]
    have : (Nat.totient 6 : ℂ) = 2 := by
      have : Nat.totient 6 = 2 := by decide
      rw [this]; norm_num
    rw [Nat.cast_mul, this]
    field_simp [(by exact_mod_cast (Nat.totient_pos.2 hf0).ne' : ((f.totient : ℕ) : ℂ) ≠ 0)]
  have hb : (v / 6).Coprime f := by
    have h6v : 6 ∣ v := hg ▸ Nat.gcd_dvd_right m v
    have hv : v = 6 * (v / 6) := (Nat.mul_div_cancel' h6v).symm
    have : m.gcd v = 6 * f.gcd (v / 6) := by rw [hm6, hv, Nat.gcd_mul_left, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hg] at this
    have h1 : f.gcd (v / 6) = 1 := by omega
    exact Nat.coprime_comm.1 h1
  rw [hE, prod_empty, hT, hg, primChar_lift' hdvd η (v / 6) hb]
  ring
noncomputable def PhiD1 {R : Type*} [CommRing R] [DecidableEq R] (A B b2 b3 : ℂ) (w : R)
    (u : R) : ℂ :=
  (if u = 6 * w then A else 0) + (if u = 3 * w then -b2 * A else 0) +
    (if u = 2 * w then -b3 * A else 0) + (if u = w then b2 * b3 * A else 0) +
    (if u = -2 * w then B else 0)
theorem psi_PhiD1 {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (A B b2 b3 : ℂ) (w : ZMod N) :
    ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * PhiD1 A B b2 b3 w (u : ZMod N) =
      A * ψ (6 * w) - b2 * A * ψ (3 * w) - b3 * A * ψ (2 * w) + b2 * b3 * A * ψ w +
        B * ψ (-2 * w) := by
  have key : ∀ (X : ZMod N) (c : ℂ),
      ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * (if (u : ZMod N) = X then c else 0) = c * ψ X := by
    intro X c
    have := sum_indicator ψ 1 X isUnit_one
    simp only [mul_one, map_one, inv_one] at this
    rw [← this, mul_sum]
    refine sum_congr rfl (fun u _ => ?_)
    split_ifs <;> ring
  unfold PhiD1
  simp only [mul_add, sum_add_distrib, key]
  ring
theorem PhiD1_supp {R : Type*} [CommRing R] [DecidableEq R] {A B b2 b3 : ℂ} {w u : R}
    (h : PhiD1 A B b2 b3 w u ≠ 0) :
    u = 6 * w ∨ u = 3 * w ∨ u = 2 * w ∨ u = w ∨ u = -2 * w := by
  by_contra hno
  push Not at hno
  apply h
  unfold PhiD1
  rw [if_neg hno.1, if_neg hno.2.1, if_neg hno.2.2.1, if_neg hno.2.2.2.1, if_neg hno.2.2.2.2]
  ring
end D
theorem f_facts {m' : ℕ} (hm'0 : m' ≠ 0) (hv3 : m'.factorization 3 = 1) :
    m' = 3 * (m' / 3) ∧ ¬ 3 ∣ m' / 3 := by
  have h3 : 3 ∣ m' := by have := Nat.ordProj_dvd m' 3; rw [hv3, pow_one] at this; exact this
  refine ⟨(Nat.mul_div_cancel' h3).symm, ?_⟩
  intro h9
  have h9' : 3 ^ 2 ∣ m' := by
    obtain ⟨t, ht⟩ := h9
    exact ⟨t, by rw [← Nat.mul_div_cancel' h3, ht]; ring⟩
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hm'0).1 h9'
  omega
theorem sum3_nat (a : Fin 3 → ℕ) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    a i + a j + a k = a 0 + a 1 + a 2 := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
    | omega
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega)
section D2
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']
theorem no_wrap (hpm : ¬ p ∣ m) (hm : m = 2 * m') (hodd : m' % 2 = 1) (a : Fin 3 → ℕ)
    (hpos : ∀ t, 0 < a t) (hsum : a 0 + a 1 + a 2 = p ^ r * m) (i j k : Fin 3) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hpd : p ^ r ∣ a i + a j) (hm'd : m' ∣ a i + a j)
    (h2d : 2 ∣ a i + a j) : False := by
  have h2m' : (2 : ℕ).Coprime m' := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
  have hmd : m ∣ a i + a j := hm ▸ Nat.Coprime.mul_dvd_of_dvd_of_dvd h2m' h2d hm'd
  have hn : p ^ r * m ∣ a i + a j :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Erdos634.LemmaSPhi.cop_pr hpm) hpd hmd
  have h3 := sum3_nat a i j k hij hik hjk
  have := Nat.le_of_dvd (by have := hpos i; omega) hn
  have := hpos k
  omega
theorem lemmaD2 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) (hpos : ∀ t, 0 < a t)
    (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0)
    (hfi : ¬ p ∣ a i ∧ (a i).Coprime m') (hfj : ¬ p ∣ a j ∧ (a j).Coprime m')
    (hβ : (a j : ZMod (p ^ r)) = -(a i : ZMod (p ^ r))) :
    e i = 0 ∧ e j = 0 := by
  have rel := top_rel_all hp7 hr hpm hm hodd hdvd a e hsum hP i j k hij hik hjk hi hj hk hfi hfj
    (-1) (Or.inr rfl) (by rw [hβ]; push_cast; ring)
  obtain ⟨z, hz⟩ := zrep (d := m') (a i) (a j) hfj.2 (-1) (Or.inr rfl)
  rcases Erdos634.LemmaSL.rel_Gprime (d := m') (by omega) (e i) (e j) (a i) (a j) hfi.2 hfj.2 (-1)
    (Or.inr rfl) z hz rel with h | ⟨hSp, hE⟩
  · exact h
  have hzm : ((z : ℤ) : ZMod m') * (-(a j : ZMod m')) = a i := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hz
    push_cast at this; linear_combination this
  have hz1 : ¬ z ≡ 1 [ZMOD m'] := by
    intro h1
    have hz1' : ((z : ℤ) : ZMod m') = 1 := by
      have := (ZMod.intCast_eq_intCast_iff z 1 m').2 h1; simpa using this
    rw [hz1'] at hzm
    refine no_wrap hpm hm hodd a hpos hsum i j k hij hik hjk ?_ ?_ (by omega)
    · rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hβ]; ring
    · rw [← ZMod.natCast_eq_zero_iff]; push_cast; linear_combination -hzm
  obtain ⟨hv3, hz3, hzf, htau⟩ := sp_odd (NeZero.ne m') hodd hSp hz1
  rw [htau] at hE
  have hE' : e j = -e i := by rw [hE]; push_cast; ring
  obtain ⟨hmf, h3f⟩ := f_facts (NeZero.ne m') hv3
  set f := m' / 3 with hf_def
  haveI : NeZero f := ⟨fun h0 => NeZero.ne m' (by omega)⟩
  have hfm' : f ∣ m' := Dvd.intro_left 3 hmf.symm
  have hfm : f ∣ m := dvd_trans hfm' hdvd
  have hfodd : f % 2 = 1 := by omega
  obtain ⟨η₂, hη₂, hev⟩ := (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne f)
    (by omega)).2 ⟨fun h => h3f (by omega), by omega⟩
  have hunitf : ∀ b : ℕ, b.Coprime f → η₂ (b : ZMod f) ≠ 0 := by
    intro b hb
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime b f).2 hb
    rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have h2f : (2 : ℕ).Coprime f := Nat.coprime_two_left.2 (Nat.odd_iff.2 hfodd)
  have h3f' : (3 : ℕ).Coprime f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f
  have hη2 : η₂ 2 ≠ 0 := by have := hunitf 2 h2f; rwa [Nat.cast_ofNat] at this
  have hη3 : η₂ 3 ≠ 0 := by have := hunitf 3 h3f'; rwa [Nat.cast_ofNat] at this
  obtain ⟨ψ, hψ, hψodd, hψ2, hψ3⟩ :=
    Erdos634.LemmaSG2Avoid.lemmaG2 hp7 hr (η₂ 2)⁻¹ (η₂ 3)⁻¹ (inv_ne_zero hη2) (inv_ne_zero hη3)
  have hodd' : (chi ψ (changeLevel hfm η₂)).Odd := by
    show (chi ψ (changeLevel hfm η₂)) (-1) = -1
    rw [MulChar.coeToFun_mul, Pi.mul_apply,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) (changeLevel hfm η₂),
      Erdos634.LemmaSG2.changeLevel_neg_one hfm η₂, show ψ (-1) = -1 from hψodd,
      show η₂ (-1) = 1 from hev, mul_one]
  have hS := hP _ hodd' (by rw [conductor_chi hpm hψ]; exact Nat.dvd_mul_right _ _)
  rw [sum3 _ i j k hij hik hjk] at hS
  have hpk : p ∣ a k := by
    have h3 := sum3_zmod (m := m) a hsum i j k hij hik hjk
    rw [hβ] at h3
    have h0 : ((a k : ℕ) : ZMod (p ^ r)) = 0 := by linear_combination h3
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact dvd_trans (dvd_pow_self p (by omega)) h0
  rw [bracket_p_dvd hr hpm hψ _ _ hpk,
    descent_term hpm hm hodd hmf h3f hfm hψ hη₂ (a i) hfi.1 hi hfi.2,
    descent_term hpm hm hodd hmf h3f hfm hψ hη₂ (a j) hfj.1 hj hfj.2] at hS
  have hψj : ψ (a j : ZMod (p ^ r)) = -ψ (a i : ZMod (p ^ r)) := by
    rw [hβ, show -(a i : ZMod (p ^ r)) = (-1) * a i by ring, map_mul, show ψ (-1) = -1 from hψodd]
    ring
  have hηj : η₂ (a j : ZMod f) = η₂ (a i : ZMod f) := by
    have hc := congrArg (ZMod.castHom hfm' (ZMod f)) hzm
    rw [map_mul, map_neg, map_intCast, map_natCast, map_natCast] at hc
    have hzf' : ((z : ℤ) : ZMod f) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff z 1 f).2 hzf; simpa using this
    rw [hzf'] at hc
    rw [show (a j : ZMod f) = (-1) * a i by linear_combination -hc, map_mul,
      show η₂ (-1) = 1 from hev, one_mul]
  rw [hψj, hηj] at hS
  have hF2 : (1 - ψ⁻¹ 2 * (η₂ 2)⁻¹) ≠ 0 := by
    intro h0
    apply hψ2
    rw [MulChar.inv_apply_eq_inv'] at h0
    apply eq_inv_of_mul_eq_one_left
    have hψ2' : ψ 2 ≠ 0 := by
      have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
      rw [Nat.cast_ofNat] at this
      obtain ⟨u, hu⟩ := this; rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    field_simp at h0
    linear_combination h0
  have hF3 : (1 - ψ⁻¹ 3 * (η₂ 3)⁻¹) ≠ 0 := by
    intro h0
    apply hψ3
    rw [MulChar.inv_apply_eq_inv'] at h0
    apply eq_inv_of_mul_eq_one_left
    have hψ3' : ψ 3 ≠ 0 := by
      have := isUnit_small (r := r) hp.out (k := 3) (by norm_num) (by norm_num) hp7
      rw [Nat.cast_ofNat] at this
      obtain ⟨u, hu⟩ := this; rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    field_simp at h0
    linear_combination h0
  have hψi : ψ (a i : ZMod (p ^ r)) ≠ 0 := by
    haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime (a i) (p ^ r)).2
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hfi.1).symm)
    rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hηi : η₂ (a i : ZMod f) ≠ 0 := hunitf _ (hfi.2.coprime_dvd_right hfm')
  have hprod : ψ (a i : ZMod (p ^ r)) * η₂ (a i : ZMod f) * (1 - ψ⁻¹ 2 * (η₂ 2)⁻¹) *
      (1 - ψ⁻¹ 3 * (η₂ 3)⁻¹) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hψi hηi) hF2) hF3
  have key : (((e i : ℚ) : ℂ) - (e j : ℚ)) * (ψ (a i : ZMod (p ^ r)) * η₂ (a i : ZMod f) *
      (1 - ψ⁻¹ 2 * (η₂ 2)⁻¹) * (1 - ψ⁻¹ 3 * (η₂ 3)⁻¹)) = 0 := by linear_combination hS
  have heq : e i = e j := by
    have := (mul_eq_zero.1 key).resolve_right hprod
    exact_mod_cast sub_eq_zero.1 this
  constructor <;> linarith
end D2
section D1
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']
set_option maxHeartbeats 1000000 in
theorem lemmaD1 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) (hpos : ∀ t, 0 < a t)
    (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0)
    (hfi : ¬ p ∣ a i ∧ (a i).Coprime m') (hfj : ¬ p ∣ a j ∧ (a j).Coprime m')
    (hβ : (a j : ZMod (p ^ r)) = (a i : ZMod (p ^ r))) (hne : a i ≠ a j) :
    e i = 0 ∧ e j = 0 := by
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  have rel := top_rel_all hp7 hr hpm hm hodd hdvd a e hsum hP i j k hij hik hjk hi hj hk hfi hfj
    1 (Or.inl rfl) (by rw [hβ]; push_cast; ring)
  obtain ⟨z, hz⟩ := zrep (d := m') (a i) (a j) hfj.2 1 (Or.inl rfl)
  rcases Erdos634.LemmaSL.rel_Gprime (d := m') (by omega) (e i) (e j) (a i) (a j) hfi.2 hfj.2 1
    (Or.inl rfl) z hz rel with h | ⟨hSp, hE⟩
  · exact h
  have hzm : ((z : ℤ) : ZMod m') * (a j : ZMod m') = a i := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hz
    push_cast at this; linear_combination this
  have h3n := sum3_nat a i j k hij hik hjk
  have hz1 : ¬ z ≡ 1 [ZMOD m'] := by
    intro h1
    have hz1' : ((z : ℤ) : ZMod m') = 1 := by
      have := (ZMod.intCast_eq_intCast_iff z 1 m').2 h1; simpa using this
    rw [hz1', one_mul] at hzm
    have h2m' : (2 : ℕ).Coprime m' := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
    have hA : a i ≡ a j [MOD 2] := by unfold Nat.ModEq; omega
    have hB : a i ≡ a j [MOD m'] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hzm.symm
    have hC := (Nat.modEq_and_modEq_iff_modEq_mul h2m').1 ⟨hA, hB⟩
    have hD : a i ≡ a j [MOD p ^ r] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hβ.symm
    have hF := (Nat.modEq_and_modEq_iff_modEq_mul
      (hm ▸ Erdos634.LemmaSPhi.cop_pr (r := r) hpm)).1 ⟨hD, hC⟩
    have := hpos i; have := hpos j; have := hpos k
    exact hne (Nat.ModEq.eq_of_lt_of_lt hF (by rw [← hm]; omega) (by rw [← hm]; omega))
  obtain ⟨hv3, hz3, hzf, htau⟩ := sp_odd (NeZero.ne m') hodd hSp hz1
  rw [htau] at hE
  have hE' : e j = e i := by rw [hE]; push_cast; ring
  obtain ⟨hmf, h3f⟩ := f_facts (NeZero.ne m') hv3
  set f := m' / 3 with hf_def
  haveI : NeZero f := ⟨fun h0 => NeZero.ne m' (by omega)⟩
  have hfm' : f ∣ m' := Dvd.intro_left 3 hmf.symm
  have hfm : f ∣ m := dvd_trans hfm' hdvd
  have h3m' : 3 ∣ m' := Dvd.intro f hmf.symm
  have hfodd : f % 2 = 1 := by omega
  have h2f : (2 : ℕ).Coprime f := Nat.coprime_two_left.2 (Nat.odd_iff.2 hfodd)
  have h3f' : (3 : ℕ).Coprime f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f
  have hijf : (a j : ZMod f) = a i := by
    have hc := congrArg (ZMod.castHom hfm' (ZMod f)) hzm
    rw [map_mul, map_intCast, map_natCast, map_natCast] at hc
    have hzf' : ((z : ℤ) : ZMod f) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff z 1 f).2 hzf; simpa using this
    rw [hzf', one_mul] at hc; exact hc
  have hsumf : ∀ d : ℕ, d ∣ m → ((a i : ℕ) : ZMod d) + a j + a k = 0 := by
    intro d hd
    have : ((a i + a j + a k : ℕ) : ZMod d) = 0 := by
      rw [h3n, hsum, Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).2 hd, mul_zero]
    push_cast at this; exact this
  have hk3 : 3 ∣ a k := by
    have hc := congrArg (ZMod.castHom h3m' (ZMod 3)) hzm
    rw [map_mul, map_intCast, map_natCast, map_natCast] at hc
    have hz3' : ((z : ℤ) : ZMod 3) = -1 := by
      have := (ZMod.intCast_eq_intCast_iff z (-1) 3).2 hz3; simpa using this
    rw [hz3'] at hc
    have hs3 := hsumf 3 (dvd_trans h3m' hdvd)
    rw [← ZMod.natCast_eq_zero_iff]; linear_combination hs3 + hc
  have hkf : (a k).Coprime f := by
    have hs := hsumf f hfm
    rw [hijf] at hs
    have hu : IsUnit ((a k : ℕ) : ZMod f) := by
      have hai : IsUnit ((a i : ℕ) : ZMod f) :=
        (ZMod.isUnit_iff_coprime _ _).2 (hfi.2.coprime_dvd_right hfm')
      have h2u : IsUnit ((2 : ℕ) : ZMod f) := (ZMod.isUnit_iff_coprime _ _).2 h2f
      rw [show ((a k : ℕ) : ZMod f) = -(((2 : ℕ) : ZMod f) * a i) by push_cast; linear_combination hs]
      exact (h2u.mul hai).neg
    exact (ZMod.isUnit_iff_coprime _ _).1 hu
  have hai : IsUnit ((a i : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime _ _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hfi.1).symm)
  have hsP := sum3_zmod (m := m) a hsum i j k hij hik hjk
  rw [hβ] at hsP
  have hkP : IsUnit ((a k : ℕ) : ZMod (p ^ r)) := by
    have h2u := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
    rw [show ((a k : ℕ) : ZMod (p ^ r)) = -(((2 : ℕ) : ZMod (p ^ r)) * a i) by
      push_cast; linear_combination hsP]
    exact (h2u.mul hai).neg
  have hpk : ¬ p ∣ a k := by
    intro hd
    have hc := (ZMod.isUnit_iff_coprime _ _).1 hkP
    have : p ∣ Nat.gcd (a k) (p ^ r) := Nat.dvd_gcd hd (dvd_pow_self p (by omega))
    rw [Nat.Coprime.gcd_eq_one hc] at this; exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
  have h6k : 6 ∣ a k := by omega
  have hm6 : m = 6 * f := by rw [hm, hmf]; ring
  have h6f : (6 : ℕ).Coprime f := Nat.Coprime.mul_left h2f h3f'
  have hg6 : m.gcd (a k) = 6 := by
    rw [hm6, Nat.gcd_comm, Nat.Coprime.gcd_mul (a k) h6f, Nat.gcd_eq_right h6k,
      Nat.Coprime.gcd_eq_one hkf]
  obtain ⟨η₂, hη₂, hev⟩ := (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne f)
    (by omega)).2 ⟨fun h => h3f (by omega), by omega⟩
  have hunitf : ∀ b : ℕ, b.Coprime f → η₂ (b : ZMod f) ≠ 0 := by
    intro b hb
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime b f).2 hb
    rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hη2 : η₂ 2 ≠ 0 := by have := hunitf 2 h2f; rwa [Nat.cast_ofNat] at this
  have hη3 : η₂ 3 ≠ 0 := by have := hunitf 3 h3f'; rwa [Nat.cast_ofNat] at this
  have hηi : η₂ (a i : ZMod f) ≠ 0 := hunitf _ (hfi.2.coprime_dvd_right hfm')
  have u2 : IsUnit (2 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have u3 : IsUnit (3 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 3) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have u5 : IsUnit (5 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 5) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  obtain ⟨k4, k6, k8, k9, k10, k12⟩ := small_units u2 u3 u5
  have k2 := u2; have k3 := u3; have k5 := u5
  set w := (6 : ZMod (p ^ r))⁻¹ * (a i : ZMod (p ^ r)) with hw_def
  have h66 : (6 : ZMod (p ^ r)) * (6 : ZMod (p ^ r))⁻¹ = 1 := ZMod.mul_inv_of_unit _ k6
  have h6w : (6 : ZMod (p ^ r)) * w = a i := by rw [hw_def, ← mul_assoc, h66, one_mul]
  have hw : IsUnit w := (IsUnit.of_mul_eq_one_right _ h66).mul hai
  have hk6 : ((a k / 6 : ℕ) : ZMod (p ^ r)) = -2 * w := by
    apply k6.mul_left_cancel
    have : (6 : ZMod (p ^ r)) * ((a k / 6 : ℕ) : ZMod (p ^ r)) = a k := by
      rw [show (6 : ZMod (p ^ r)) = ((6 : ℕ) : ZMod (p ^ r)) by norm_num, ← Nat.cast_mul,
        Nat.mul_div_cancel' h6k]
    rw [this]; linear_combination hsP + 2 * h6w
  set A : ℂ := (((e i : ℚ) : ℂ) + (e j : ℚ)) * η₂ (a i : ZMod f) with hA
  set B : ℂ := 2 * ((e k : ℚ) : ℂ) * η₂ ((a k / 6 : ℕ) : ZMod f) with hB
  set b2 : ℂ := (η₂ 2)⁻¹
  set b3 : ℂ := (η₂ 3)⁻¹
  have hvanD : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * PhiD1 A B b2 b3 w (u : ZMod (p ^ r)) = 0 := by
    intro ψ hψ hψodd
    have hodd' : (chi ψ (changeLevel hfm η₂)).Odd := by
      show (chi ψ (changeLevel hfm η₂)) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) (changeLevel hfm η₂),
        Erdos634.LemmaSG2.changeLevel_neg_one hfm η₂, hψodd, show η₂ (-1) = 1 from hev, mul_one]
    have hS := hP _ hodd' (by rw [conductor_chi hpm hψ]; exact Nat.dvd_mul_right _ _)
    rw [sum3 _ i j k hij hik hjk,
      descent_term hpm hm hodd hmf h3f hfm hψ hη₂ (a i) hfi.1 hi hfi.2,
      descent_term hpm hm hodd hmf h3f hfm hψ hη₂ (a j) hfj.1 hj hfj.2,
      descent_term_six hpm hm hodd hmf h3f hfm hψ hη₂ (a k) hpk hg6, hβ, hijf] at hS
    rw [psi_PhiD1]
    have hψ2 : ψ 2 ≠ 0 := by obtain ⟨u, hu⟩ := u2; rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    have hψ3 : ψ 3 ≠ 0 := by obtain ⟨u, hu⟩ := u3; rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    have e6 : ψ (6 * w) = ψ (a i : ZMod (p ^ r)) := by rw [h6w]
    have e3 : ψ (3 * w) = ψ (a i : ZMod (p ^ r)) * ψ⁻¹ 2 := by
      rw [MulChar.inv_apply_eq_inv', ← h6w, show (6 : ZMod (p ^ r)) * w = 2 * (3 * w) by ring,
        map_mul ψ 2 (3 * w)]; field_simp
    have e2 : ψ (2 * w) = ψ (a i : ZMod (p ^ r)) * ψ⁻¹ 3 := by
      rw [MulChar.inv_apply_eq_inv', ← h6w, show (6 : ZMod (p ^ r)) * w = 3 * (2 * w) by ring,
        map_mul ψ 3 (2 * w)]; field_simp
    have e1 : ψ w = ψ (a i : ZMod (p ^ r)) * ψ⁻¹ 2 * ψ⁻¹ 3 := by
      rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', ← h6w,
        show (6 : ZMod (p ^ r)) * w = 2 * (3 * w) by ring, map_mul ψ 2 (3 * w), map_mul ψ 3 w]
      field_simp
    have em : ψ (-2 * w) = ψ ((a k / 6 : ℕ) : ZMod (p ^ r)) := by rw [hk6]
    rw [e6, e3, e2, e1, em]
    linear_combination hS
  set Φ : (ZMod (p ^ r))ˣ → ℂ := fun v => PhiD1 A B b2 b3 w (v : ZMod (p ^ r)) with hΦ
  have hsymD : ∀ v : (ZMod (p ^ r))ˣ, Φ v = Φ (-v) := by
    rcases Nat.lt_or_ge r 2 with hr1 | hr2
    · obtain rfl : r = 1 := by omega
      exact lemmaN_b Φ hvanD
    · let T : Fin 2 → Finset (ZMod (p ^ r)) := ![G w [6, -6, 3, -3, 2, -2], G w [1, -1]]
      have hsupp : ∀ v : (ZMod (p ^ r))ˣ, Φ v ≠ 0 ∨ Φ (-v) ≠ 0 →
          ∃ t, (v : ZMod (p ^ r)) ∈ T t := by
        intro v hv
        rcases hv with hv | hv
        · rcases PhiD1_supp hv with h1 | h1 | h1 | h1 | h1
          · exact ⟨0, mem_G 6 (by simp) (by rw [h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G 3 (by simp) (by rw [h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G 2 (by simp) (by rw [h1]; push_cast; ring)⟩
          · exact ⟨1, mem_G 1 (by simp) (by rw [h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G (-2) (by simp) (by rw [h1]; push_cast; ring)⟩
        · simp only [Φ, Units.val_neg] at hv
          rcases PhiD1_supp hv with h1 | h1 | h1 | h1 | h1
          · exact ⟨0, mem_G (-6) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G (-3) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G (-2) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
          · exact ⟨1, mem_G (-1) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G 2 (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
      have hinj : ∀ t, ∀ x ∈ T t, ∀ y ∈ T t, IsUnit x → IsUnit y →
          ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) x =
            ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) y → x = y := by
        intro t
        fin_cases t
        · exact inj_group hp7 (by omega) [6, -6, 3, -3, 2, -2] (by decide) w
        · exact inj_group hp7 (by omega) [1, -1] (by decide) w
      intro v
      have := lemmaN_groups hr2 Φ (ε := -1) (Or.inr rfl) hvanD (k := 2) (by omega) T hsupp hinj v
      rw [this]; ring
  obtain ⟨U, hU⟩ := u3.mul hw
  have E := hsymD U
  simp only [Φ, Units.val_neg, hU] at E
  simp (disch := first | ring1 | (first | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1) | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1) | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1) | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1) | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1) | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1) | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1) | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1) | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1) | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1)) | assumption) only [PhiD1, if_pos, if_neg, ↓reduceIte] at E
  have hA0 : A = 0 := by
    have : b2 * A = 0 := by linear_combination -E
    exact (mul_eq_zero.1 this).resolve_left (inv_ne_zero hη2)
  have hsum0 : (((e i : ℚ) : ℂ) + (e j : ℚ)) = 0 := (mul_eq_zero.1 hA0).resolve_right hηi
  have : e i + e j = 0 := by exact_mod_cast hsum0
  constructor <;> linarith
end D1
end Erdos634.LemmaSEvenD
end

section
open scoped BigOperators
open Finset
namespace Erdos634.LemmaSEven
open DirichletCharacter
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (dm)
open Erdos634.LemmaSElim (classSum lemmaElim)
open Erdos634.LemmaSIso (fpc)
open Erdos634.LemmaSEvenT (Phi5)
open Erdos634.LemmaSEvenComp
open Erdos634.LemmaSEvenTop
open Erdos634.LemmaSEvenD
theorem exists_ijk (a : Fin 3 → ℕ) (hs : (a 0 + a 1 + a 2) % 2 = 0)
    (h2 : ¬ (2 ∣ a 0 ∧ 2 ∣ a 1 ∧ 2 ∣ a 2)) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ a i % 2 = 1 ∧ a j % 2 = 1 ∧ a k % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (a 0) with h0 | h0 <;>
  rcases Nat.mod_two_eq_zero_or_one (a 1) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (a 2) with h3 | h3
  · exact absurd ⟨Nat.dvd_of_mod_eq_zero h0, Nat.dvd_of_mod_eq_zero h1, Nat.dvd_of_mod_eq_zero h3⟩ h2
  · omega
  · omega
  · exact ⟨1, 2, 0, by decide, by decide, by decide, h1, h3, h0⟩
  · omega
  · exact ⟨0, 2, 1, by decide, by decide, by decide, h0, h3, h1⟩
  · exact ⟨0, 1, 2, by decide, by decide, by decide, h0, h1, h3⟩
  · omega
theorem sum3q (f : Fin 3 → ℚ) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ t, f t = f i + f j + f k := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
    | (simp [Fin.sum_univ_three]; done) | (simp [Fin.sum_univ_three]; ring)
theorem fin3_cover (t i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    t = i ∨ t = j ∨ t = k := by
  revert t i j k; decide
section Full
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']
theorem fullEven (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hexc : ¬ (r = 1 ∧ m' = 3 ∧ p < 13)) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hpos : ∀ t, 0 < a t) (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ univ.image a) (hpx : ¬ p ∣ x) (hxm : x.Coprime m') :
    classSum a e x = 0 := by
  have hdvd : m' ∣ m := Dvd.intro_left 2 hm.symm
  have hs2 : (a 0 + a 1 + a 2) % 2 = 0 := by
    rw [hsum, hm]; simp [Nat.mul_mod]
  have h2 : ¬ (2 ∣ a 0 ∧ 2 ∣ a 1 ∧ 2 ∣ a 2) := by
    rintro ⟨h0, h1, h3⟩
    have := Nat.dvd_gcd h0 (Nat.dvd_gcd h1 h3)
    rw [hgcd] at this; omega
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := exists_ijk a hs2 h2
  have hm'4 : m' % 4 ≠ 2 := by omega
  obtain ⟨η, hη, hcase⟩ : ∃ η : DirichletCharacter ℂ m', η.IsPrimitive ∧
      (2 ≤ r ∨ (r = 1 ∧ (η.Even ∨ ∃ P : Finset (ZMod (p ^ r)),
        (∀ v : ZMod (p ^ r), IsUnit v → (PhiTop p r m' η a e i j k v ≠ 0 ∨
          PhiTop p r m' η a e i j k (-v) ≠ 0) → v ∈ P) ∧ P.card < p - 1))) := by
    by_cases hr2 : 2 ≤ r
    · obtain ⟨η, hη⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne m') hm'4
      exact ⟨η, hη, Or.inl hr2⟩
    have hr1 : r = 1 := by omega
    by_cases h3 : m' = 3
    · obtain ⟨η, hη⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne m') hm'4
      have hp13 : 13 ≤ p := by
        by_contra hlt; exact hexc ⟨hr1, h3, by omega⟩
      refine ⟨η, hη, Or.inr ⟨hr1, Or.inr ⟨(
        [2 * ((2 : ZMod (p ^ r))⁻¹ * a i), -(2 * ((2 : ZMod (p ^ r))⁻¹ * a i)),
         (2 : ZMod (p ^ r))⁻¹ * a i, -((2 : ZMod (p ^ r))⁻¹ * a i),
         2 * ((2 : ZMod (p ^ r))⁻¹ * a j), -(2 * ((2 : ZMod (p ^ r))⁻¹ * a j)),
         (2 : ZMod (p ^ r))⁻¹ * a j, -((2 : ZMod (p ^ r))⁻¹ * a j),
         ((a k / 2 : ℕ) : ZMod (p ^ r)), -((a k / 2 : ℕ) : ZMod (p ^ r))]).toFinset, ?_, ?_⟩⟩⟩
      · intro v _ hv
        rw [List.mem_toFinset]
        rcases hv with hv | hv
        · rcases PhiTop_supp hp7 η a e i j k v hv with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> simp
        · rcases PhiTop_supp hp7 η a e i j k (-v) hv with h1 | h1 | h1 | h1 | h1 <;>
            rw [← neg_neg v, h1] <;> simp
      · exact lt_of_le_of_lt (List.toFinset_card_le _) (by simp; omega)
    · obtain ⟨η, hη, hev⟩ := (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne m')
        hm'4).2 ⟨h3, by omega⟩
      exact ⟨η, hη, Or.inr ⟨hr1, Or.inl hev⟩⟩
  have hsym := top_sym hp7 hr hpm hm hodd hdvd hη a e hP i j k hij hik hjk hi hj hk hcase
  obtain ⟨hk0, hT⟩ := top_T hp7 hr hpm hm hodd hdvd hη a e hsum i j k hij hik hjk hk hsym
  have hηne : ∀ b : ℕ, b.Coprime m' → η (b : ZMod m') ≠ 0 := by
    intro b hb
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime b m').2 hb
    rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hcodd : ∀ t, a t % 2 = 1 → ¬ p ∣ a t ∧ (a t).Coprime m' →
      cT p m' η a e t = (e t : ℂ) * η (a t : ZMod m') := by
    intro t ht hf; unfold cT; rw [if_pos hf, if_pos ht]
  have hcnf : ∀ t, ¬ (¬ p ∣ a t ∧ (a t).Coprime m') → cT p m' η a e t = 0 := by
    intro t hf; unfold cT; rw [if_neg hf]
  have hzero : ∀ t, a t % 2 = 1 → ¬ p ∣ a t ∧ (a t).Coprime m' → cT p m' η a e t = 0 →
      e t = 0 := by
    intro t ht hf h0
    rw [hcodd t ht hf] at h0
    exact_mod_cast (mul_eq_zero.1 h0).resolve_right (hηne _ hf.2)
  have hcs : classSum a e x = (if a i = x then e i else 0) + (if a j = x then e j else 0) +
      (if a k = x then e k else 0) := by
    unfold classSum; rw [sum_filter, sum3q _ i j k hij hik hjk]
  have hfx : ¬ p ∣ x ∧ x.Coprime m' := ⟨hpx, hxm⟩
  rw [hcs]
  by_cases hkx : a k = x
  · 
    have hix : a i ≠ x := fun h => by omega
    have hjx : a j ≠ x := fun h => by omega
    rw [if_neg hix, if_neg hjx, if_pos hkx]
    have hf : ¬ p ∣ a k ∧ (a k).Coprime m' := hkx ▸ hfx
    have hk' : ¬ a k % 2 = 1 := by omega
    unfold cT at hk0
    rw [if_pos hf, if_neg hk'] at hk0
    have hb : (a k / 2).Coprime m' :=
      Nat.Coprime.coprime_dvd_left (Dvd.intro_left 2 (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk))) hf.2
    simp only [zero_add]
    exact_mod_cast (mul_eq_zero.1 hk0).resolve_right (hηne _ hb)
  rw [if_neg hkx, add_zero]
  by_cases hix : a i = x <;> by_cases hjx : a j = x
  · 
    have hfi : ¬ p ∣ a i ∧ (a i).Coprime m' := hix ▸ hfx
    have hfj : ¬ p ∣ a j ∧ (a j).Coprime m' := hjx ▸ hfx
    rw [if_pos hix, if_pos hjx]
    have hij' : a i = a j := hix.trans hjx.symm
    rcases hT with ⟨h1, h2⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [hzero i hi hfi h1, hzero j hj hfj h2, add_zero]
    · rw [hcodd i hi hfi, hcodd j hj hfj, show (a j : ZMod m') = a i by rw [hij']] at h
      have : (((e i : ℚ) : ℂ) + (e j : ℚ)) * η (a i : ZMod m') = 0 := by linear_combination h
      exact_mod_cast (mul_eq_zero.1 this).resolve_right (hηne _ hfi.2)
    · exfalso
      rw [hij'] at h
      have h2u := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
      haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
      have hju : IsUnit ((a j : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime _ _).2
        (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hfj.1).symm)
      have : ((2 : ℕ) : ZMod (p ^ r)) * a j = 0 := by push_cast; linear_combination h
      exact (h2u.mul hju).ne_zero this
  · 
    have hfi : ¬ p ∣ a i ∧ (a i).Coprime m' := hix ▸ hfx
    rw [if_pos hix, if_neg hjx, add_zero]
    by_cases hfj : ¬ p ∣ a j ∧ (a j).Coprime m'
    · have hne : a i ≠ a j := fun h => hjx (h ▸ hix)
      rcases hT with ⟨h1, -⟩ | ⟨hβ, -⟩ | ⟨hβ, -⟩
      · exact hzero i hi hfi h1
      · exact (lemmaD1 hp7 hr hpm hm hodd hdvd a e hpos hsum hP i j k hij hik hjk hi hj hk hfi hfj
          hβ hne).1
      · exact (lemmaD2 hp7 hr hpm hm hodd hdvd a e hpos hsum hP i j k hij hik hjk hi hj hk hfi hfj
          hβ).1
    · have hcj := hcnf j hfj
      rcases hT with ⟨h1, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact hzero i hi hfi h1
      · exact hzero i hi hfi (by rw [hcj, add_zero] at h; exact h)
      · exact hzero i hi hfi (by rw [hcj, mul_zero] at h; exact h)
  · 
    have hfj : ¬ p ∣ a j ∧ (a j).Coprime m' := hjx ▸ hfx
    rw [if_neg hix, if_pos hjx, zero_add]
    by_cases hfi : ¬ p ∣ a i ∧ (a i).Coprime m'
    · have hne : a i ≠ a j := fun h => hix (h ▸ hjx)
      rcases hT with ⟨-, h2⟩ | ⟨hβ, -⟩ | ⟨hβ, -⟩
      · exact hzero j hj hfj h2
      · exact (lemmaD1 hp7 hr hpm hm hodd hdvd a e hpos hsum hP i j k hij hik hjk hi hj hk hfi hfj
          hβ hne).2
      · exact (lemmaD2 hp7 hr hpm hm hodd hdvd a e hpos hsum hP i j k hij hik hjk hi hj hk hfi hfj
          hβ).2
    · have hci := hcnf i hfi
      have hη1 : η (-1) ≠ 0 := by
        rcases η.even_or_odd with h | h
        · rw [show η (-1) = 1 from h]; exact one_ne_zero
        · rw [show η (-1) = -1 from h]; norm_num
      rcases hT with ⟨-, h2⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact hzero j hj hfj h2
      · exact hzero j hj hfj (by rw [hci, zero_add] at h; exact h)
      · rw [hci] at h
        exact hzero j hj hfj ((mul_eq_zero.1 h.symm).resolve_left hη1)
  · 
    exfalso
    obtain ⟨t, -, ht⟩ := mem_image.1 hx
    have : t = i ∨ t = j ∨ t = k := fin3_cover t i j k hij hik hjk
    rcases this with rfl | rfl | rfl
    · exact hix ht
    · exact hjx ht
    · exact hkx ht
end Full
theorem cop_of_fpc {m m' x : ℕ} (hm : m = 2 * m') (hodd : m' % 2 = 1) (hm'0 : 0 < m')
    (h : fpc m ∣ dm m x) : x.Coprime m' := by
  have hfpc : fpc m = m' := by
    unfold fpc; rw [if_pos (by omega), hm, Nat.mul_div_cancel_left m' (by norm_num)]
  rw [hfpc] at h
  have hg : m.gcd x ∣ m := Nat.gcd_dvd_left _ _
  obtain ⟨t, ht⟩ := h
  have h1 : m = m' * t * m.gcd x := by
    unfold dm at ht; rw [← ht, Nat.div_mul_cancel hg]
  have h2 : m.gcd x * t = 2 := by
    have : m' * (m.gcd x * t) = m' * 2 := by
      rw [show m' * (m.gcd x * t) = m' * t * m.gcd x by ring, ← h1, hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hm'0 this
  have hg2 : m.gcd x ∣ 2 := Dvd.intro t h2
  have hdvd : m' ∣ m := Dvd.intro_left 2 hm.symm
  have hd1 : x.gcd m' ∣ m.gcd x :=
    Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_right x m') hdvd) (Nat.gcd_dvd_left x m')
  rcases (Nat.dvd_prime Nat.prime_two).1 (dvd_trans hd1 hg2) with h | h
  · exact h
  · have : 2 ∣ m' := h ▸ Nat.gcd_dvd_right x m'
    omega
theorem lemmaS_even {p r m : ℕ} [hp : Fact p.Prime] [NeZero m] (hp7 : 7 ≤ p) (hr : 1 ≤ r)
    (hpm : ¬ p ∣ m) (hm4 : m % 4 = 2)
    (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = p ^ r * m)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (p ^ r * m) a = trivSpace (p ^ r * m) a := by
  haveI : NeZero (p ^ r * m) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m)⟩
  have hsum3 : a 0 + a 1 + a 2 = p ^ r * m := by rw [← hsum, Fin.sum_univ_three]
  by_cases hexc : r = 1 ∧ m / 2 = 3 ∧ p < 13
  · obtain ⟨rfl, h3, hp13⟩ := hexc
    have hm6 : m = 6 := by omega
    subst hm6
    have hp' : p = 7 ∨ p = 11 := by
      have := hp.out
      interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; revert this; decide)
    have hn : p ^ 1 * 6 = 21 ∨ p ^ 1 * 6 = 28 ∨ p ^ 1 * 6 = 42 ∨ p ^ 1 * 6 = 66 := by
      rcases hp' with rfl | rfl <;> norm_num
    exact Erdos634.LemmaS.lemmaS_finite hn a hpos hsum hgcd
  set m' := m / 2 with hm'_def
  have hm : m = 2 * m' := by omega
  have hodd : m' % 2 = 1 := by omega
  haveI : NeZero m' := ⟨by omega⟩
  have hgcd' : univ.gcd a = 1 := by
    apply Nat.eq_one_of_dvd_one
    rw [← hgcd]
    exact Nat.dvd_gcd (Finset.gcd_dvd (mem_univ 0))
      (Nat.dvd_gcd (Finset.gcd_dvd (mem_univ 1)) (Finset.gcd_dvd (mem_univ 2)))
  refine Erdos634.LemmaSR.lemmaR a hpos hsum hgcd hp.out
    (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m) (fun e he j hpj => ?_)
  have hcrit := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he
  have hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0 := fun χ ho _ => hcrit χ ho
  have hall := lemmaElim hp7 hr hpm a e hsum3 hgcd' hP (fun x hx hpx hfull =>
    fullEven hp7 hr hpm hm hodd hexc a e hpos hsum3 hgcd hP x hx hpx
      (cop_of_fpc hm hodd (by omega) hfull)) (a j) (mem_image_of_mem a (mem_univ j)) hpj
  unfold classSum at hall
  rw [filter_filter]
  rw [← hall]
  refine sum_congr ?_ (fun _ _ => rfl)
  ext k
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rw [h]; exact hpj, h⟩
end Erdos634.LemmaSEven
end

section
open scoped BigOperators
namespace Erdos634.LemmaSAll
open Erdos634.LemmaS (relSpace trivSpace)
theorem lemmaS : Erdos634.CaseA.R0c.LemmaSStatement := by
  intro n a hpos hsum hgcd p hp hp7 hpn
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by
    have := hpos 0; rw [← hsum, Fin.sum_univ_three]; omega
  obtain ⟨r, m, rfl, hr, hpm, hm0⟩ : ∃ r m : ℕ, n = p ^ r * m ∧ 1 ≤ r ∧ ¬ p ∣ m ∧ m ≠ 0 :=
    ⟨n.factorization p, n / p ^ n.factorization p, (Nat.ordProj_mul_ordCompl_eq_self n p).symm,
      (hp.dvd_iff_one_le_factorization hn0).1 hpn, Nat.not_dvd_ordCompl hp hn0,
      (Nat.ordCompl_pos p hn0).ne'⟩
  haveI : NeZero m := ⟨hm0⟩
  by_cases hm4 : m % 4 = 2
  · exact Erdos634.LemmaSEven.lemmaS_even hp7 hr hpm hm4 a hpos hsum hgcd
  · exact Erdos634.LemmaSOddAll.lemmaS_oddAll hp7 hr hpm hm4 a hpos hsum hgcd
end Erdos634.LemmaSAll
end



/-- Lemma S (Bonfioli): when a prime at least 7 divides n, the relation space is trivial.
The flattened development above is the one of erdos-634.R1.H3.R1.H2.R1.H2. -/
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro n a hpos hsum hg h
  obtain ⟨l, hl, h7, hd⟩ := h
  exact Erdos634.LemmaSAll.lemmaS n a hpos hsum hg l hl h7 hd
