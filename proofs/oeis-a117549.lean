import OMAStatements.S_oeis_a117549

-- Problem: A117549: Values of n for which there exist d(1),...,d(n), each in {0,1,...,4} and an r in {1,...,4} such that Sum[d(i)d(i+k),i=1,n-k]=r (mod 5) for all k=0,...,n-1. (Such a sequence is called a very(5,r) sequence. See the link.).
-- Upstream: formal-conjectures statements/oeis-a117549.lean:0 (declaration OMA.S_oeis_a117549.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: write n = m + 1 and s = 2m + 1. The blocks A, 3A, A of AZ(3A)ZA start at 0, s and 2s
-- and are separated by m zeros. Splitting the correlation sum at the block borders, the
-- correlation of AZ(3A)ZA at k is 11 C(k) for k <= m, 6 C(|k - s|) for m < k < s + m + 1 and
-- C(|k - 2s|) beyond (mod 5), where C is the correlation of A; each is r mod 5.

open OMA.S_oeis_a117549 in
theorem OMA.solution : type_of% @OMA.S_oeis_a117549.main := by
  intro r _ A hA
  obtain ⟨hA1, hA2⟩ := hA
  have hlen : (glue A).length = 5 * A.length - 2 := by
    simp only [glue, List.length_append, List.length_replicate, List.length_map]
    omega
  obtain ⟨Z, hZ⟩ : ∃ Z : List ℕ, Z = List.replicate (A.length - 1) 0 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : List ℕ, M = List.map (fun x => 3 * x % 5) A := ⟨_, rfl⟩
  have hG : glue A = A ++ Z ++ M ++ Z ++ A := by
    subst hZ hM
    rfl
  refine ⟨⟨?_, ?_⟩, hlen⟩
  · intro x hx
    rw [hG] at hx
    simp only [List.mem_append] at hx
    rcases hx with (((h | h) | h) | h) | h
    · exact hA1 x h
    · rw [hZ, List.mem_replicate] at h
      omega
    · rw [hM, List.mem_map] at h
      obtain ⟨y, -, rfl⟩ := h
      omega
    · rw [hZ, List.mem_replicate] at h
      omega
    · exact hA1 x h
  · intro k hk
    rw [hlen] at hk
    obtain ⟨m, hm⟩ : ∃ m, A.length = m + 1 := ⟨A.length - 1, by omega⟩
    have lZ : Z.length = m := by
      rw [hZ, List.length_replicate]
      omega
    have lM : M.length = m + 1 := by
      rw [hM, List.length_map, hm]
    have l2 : (A ++ Z).length = 2 * m + 1 := by
      rw [List.length_append, hm, lZ]
      omega
    have l3 : (A ++ Z ++ M).length = 3 * m + 2 := by
      rw [List.length_append, l2, lM]
      omega
    have l4 : (A ++ Z ++ M ++ Z).length = 4 * m + 2 := by
      rw [List.length_append, l3, lZ]
      omega
    have hZ0 : ∀ i, Z.getD i 0 = 0 := by
      intro i
      rw [hZ, List.getD_eq_getElem?_getD]
      simp
    have hM0 : ∀ j, M.getD j 0 = 3 * A.getD j 0 % 5 := by
      intro j
      rw [hM]
      exact List.getD_map (l := A) (d := 0) (fun x => 3 * x % 5)
    obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ, ∀ j, A.getD j 0 = a j := ⟨fun j => A.getD j 0, fun _ => rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ j, (A ++ Z ++ M ++ Z ++ A).getD j 0 = b j :=
      ⟨fun j => (A ++ Z ++ M ++ Z ++ A).getD j 0, fun _ => rfl⟩
    -- the terms of AZ(3A)ZA, block by block
    have hbA : ∀ i, i < m + 1 → b i = a i := by
      intro i hi
      rw [← hb, ← ha, List.getD_append (A ++ Z ++ M ++ Z) A 0 i (by rw [l4]; omega),
        List.getD_append (A ++ Z ++ M) Z 0 i (by rw [l3]; omega),
        List.getD_append (A ++ Z) M 0 i (by rw [l2]; omega),
        List.getD_append A Z 0 i (by rw [hm]; omega)]
    have hbZ1 : ∀ i, m + 1 ≤ i → i < 2 * m + 1 → b i = 0 := by
      intro i h1 h2
      rw [← hb, List.getD_append (A ++ Z ++ M ++ Z) A 0 i (by rw [l4]; omega),
        List.getD_append (A ++ Z ++ M) Z 0 i (by rw [l3]; omega),
        List.getD_append (A ++ Z) M 0 i (by rw [l2]; omega),
        List.getD_append_right A Z 0 i (by rw [hm]; omega), hZ0]
    have hbM : ∀ i, 2 * m + 1 ≤ i → i < 3 * m + 2 → b i = 3 * a (i - (2 * m + 1)) % 5 := by
      intro i h1 h2
      rw [← hb, ← ha, List.getD_append (A ++ Z ++ M ++ Z) A 0 i (by rw [l4]; omega),
        List.getD_append (A ++ Z ++ M) Z 0 i (by rw [l3]; omega),
        List.getD_append_right (A ++ Z) M 0 i (by rw [l2]; omega), hM0, l2]
    have hbZ2 : ∀ i, 3 * m + 2 ≤ i → i < 4 * m + 2 → b i = 0 := by
      intro i h1 h2
      rw [← hb, List.getD_append (A ++ Z ++ M ++ Z) A 0 i (by rw [l4]; omega),
        List.getD_append_right (A ++ Z ++ M) Z 0 i (by rw [l3]; omega), hZ0]
    have hbA2 : ∀ i, 4 * m + 2 ≤ i → b i = a (i - (4 * m + 2)) := by
      intro i h1
      rw [← hb, ← ha, List.getD_append_right (A ++ Z ++ M ++ Z) A 0 i (by rw [l4]; omega), l4]
    have hS : corr (glue A) k = ∑ i ∈ Finset.range (5 * m + 3 - k), b i * b (i + k) := by
      unfold corr
      rw [hlen, hm, hG, show 5 * (m + 1) - 2 - k = 5 * m + 3 - k by omega]
      simp only [hb]
    have hT : ∀ p, p < m + 1 → ∑ j ∈ Finset.range (m + 1 - p),
        ((a j : ℕ) : ZMod 5) * ((a (j + p) : ℕ) : ZMod 5) = (r : ZMod 5) := by
      intro p hp
      have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hA2 p (by omega))
      unfold corr at h
      rw [hm] at h
      simp only [ha, Nat.cast_sum, Nat.cast_mul] at h
      exact h
    have h5 : (5 : ZMod 5) = 0 := by decide
    rw [← ZMod.natCast_eq_natCast_iff, hS]
    rcases Nat.lt_or_ge k (m + 1) with c1 | c1
    · -- k <= m: three block sums C(k), 9 C(k), C(k)
      have p1 : ∀ x ∈ Finset.range (m + 1 - k), b x * b (x + k) = a x * a (x + k) := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbA x (by omega), hbA (x + k) (by omega)]
      have p2 : ∀ x ∈ Finset.range (m + k), b (m + 1 - k + x) * b (m + 1 - k + x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rcases Nat.lt_or_ge (m + 1 - k + x) (m + 1) with h | h
        · rw [hbZ1 (m + 1 - k + x + k) (by omega) (by omega), mul_zero]
        · rw [hbZ1 (m + 1 - k + x) h (by omega), zero_mul]
      have p3 : ∀ x ∈ Finset.range (m + 1 - k),
          b (2 * m + 1 + x) * b (2 * m + 1 + x + k) = 3 * a x % 5 * (3 * a (x + k) % 5) := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbM (2 * m + 1 + x) (by omega) (by omega),
          hbM (2 * m + 1 + x + k) (by omega) (by omega),
          show 2 * m + 1 + x - (2 * m + 1) = x by omega,
          show 2 * m + 1 + x + k - (2 * m + 1) = x + k by omega]
      have p4 : ∀ x ∈ Finset.range (m + k),
          b (3 * m + 2 - k + x) * b (3 * m + 2 - k + x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rcases Nat.lt_or_ge (3 * m + 2 - k + x) (3 * m + 2) with h | h
        · rw [hbZ2 (3 * m + 2 - k + x + k) (by omega) (by omega), mul_zero]
        · rw [hbZ2 (3 * m + 2 - k + x) h (by omega), zero_mul]
      have p5 : ∀ x ∈ Finset.range (m + 1 - k),
          b (4 * m + 2 + x) * b (4 * m + 2 + x + k) = a x * a (x + k) := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbA2 (4 * m + 2 + x) (by omega), hbA2 (4 * m + 2 + x + k) (by omega),
          show 4 * m + 2 + x - (4 * m + 2) = x by omega,
          show 4 * m + 2 + x + k - (4 * m + 2) = x + k by omega]
      have r1 : Finset.range (5 * m + 3 - k) = Finset.range (4 * m + 2 + (m + 1 - k)) :=
        congrArg Finset.range (by omega)
      have r2 : Finset.range (4 * m + 2) = Finset.range (3 * m + 2 - k + (m + k)) :=
        congrArg Finset.range (by omega)
      have r3 : Finset.range (3 * m + 2 - k) = Finset.range (2 * m + 1 + (m + 1 - k)) :=
        congrArg Finset.range (by omega)
      have r4 : Finset.range (2 * m + 1) = Finset.range (m + 1 - k + (m + k)) :=
        congrArg Finset.range (by omega)
      have e : ∑ i ∈ Finset.range (5 * m + 3 - k), b i * b (i + k) =
          ∑ j ∈ Finset.range (m + 1 - k), a j * a (j + k) +
          ∑ j ∈ Finset.range (m + 1 - k), 3 * a j % 5 * (3 * a (j + k) % 5) +
          ∑ j ∈ Finset.range (m + 1 - k), a j * a (j + k) := by
        rw [r1, Finset.sum_range_add (fun i => b i * b (i + k)) (4 * m + 2) (m + 1 - k), r2,
          Finset.sum_range_add (fun i => b i * b (i + k)) (3 * m + 2 - k) (m + k), r3,
          Finset.sum_range_add (fun i => b i * b (i + k)) (2 * m + 1) (m + 1 - k), r4,
          Finset.sum_range_add (fun i => b i * b (i + k)) (m + 1 - k) (m + k),
          Finset.sum_congr rfl p1, Finset.sum_eq_zero p2, Finset.sum_congr rfl p3,
          Finset.sum_eq_zero p4, Finset.sum_congr rfl p5]
        simp only [add_zero]
      rw [e, Nat.cast_add, Nat.cast_add]
      have q1 : ((∑ j ∈ Finset.range (m + 1 - k), a j * a (j + k) : ℕ) : ZMod 5) =
          ∑ j ∈ Finset.range (m + 1 - k), ((a j : ℕ) : ZMod 5) * ((a (j + k) : ℕ) : ZMod 5) := by
        simp only [Nat.cast_sum, Nat.cast_mul]
      have q3 : ((∑ j ∈ Finset.range (m + 1 - k), 3 * a j % 5 * (3 * a (j + k) % 5) : ℕ) :
          ZMod 5) = 9 * ∑ j ∈ Finset.range (m + 1 - k),
            ((a j : ℕ) : ZMod 5) * ((a (j + k) : ℕ) : ZMod 5) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.cast_mul, ZMod.natCast_mod, ZMod.natCast_mod]
        push_cast
        ring
      rw [q1, q3, hT k c1]
      linear_combination (2 * (r : ZMod 5)) * h5
    rcases Nat.lt_or_ge k (2 * m + 1) with c2 | c2
    · -- m < k < s: with p = s - k, two block sums 3 C(p) and 3 C(p)
      obtain ⟨p, hp⟩ : ∃ p, k + p = 2 * m + 1 := ⟨2 * m + 1 - k, by omega⟩
      have pa : ∀ x ∈ Finset.range p, b x * b (x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbZ1 (x + k) (by omega) (by omega), mul_zero]
      have pb : ∀ x ∈ Finset.range (m + 1 - p),
          b (p + x) * b (p + x + k) = a (x + p) * (3 * a x % 5) := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbA (p + x) (by omega), hbM (p + x + k) (by omega) (by omega),
          show p + x + k - (2 * m + 1) = x by omega, Nat.add_comm p x]
      have pc : ∀ x ∈ Finset.range m, b (m + 1 + x) * b (m + 1 + x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbZ1 (m + 1 + x) (by omega) (by omega), zero_mul]
      have pd : ∀ x ∈ Finset.range p, b (2 * m + 1 + x) * b (2 * m + 1 + x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbZ2 (2 * m + 1 + x + k) (by omega) (by omega), mul_zero]
      have pe : ∀ x ∈ Finset.range (m + 1 - p),
          b (2 * m + 1 + p + x) * b (2 * m + 1 + p + x + k) = 3 * a (x + p) % 5 * a x := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbM (2 * m + 1 + p + x) (by omega) (by omega),
          hbA2 (2 * m + 1 + p + x + k) (by omega),
          show 2 * m + 1 + p + x - (2 * m + 1) = x + p by omega,
          show 2 * m + 1 + p + x + k - (4 * m + 2) = x by omega]
      have pf : ∀ x ∈ Finset.range p, b (3 * m + 2 + x) * b (3 * m + 2 + x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbZ2 (3 * m + 2 + x) (by omega) (by omega), zero_mul]
      have r1 : Finset.range (5 * m + 3 - k) = Finset.range (3 * m + 2 + p) :=
        congrArg Finset.range (by omega)
      have r2 : Finset.range (3 * m + 2) = Finset.range (2 * m + 1 + p + (m + 1 - p)) :=
        congrArg Finset.range (by omega)
      have r4 : Finset.range (2 * m + 1) = Finset.range (m + 1 + m) :=
        congrArg Finset.range (by omega)
      have r5 : Finset.range (m + 1) = Finset.range (p + (m + 1 - p)) :=
        congrArg Finset.range (by omega)
      have e : ∑ i ∈ Finset.range (5 * m + 3 - k), b i * b (i + k) =
          ∑ j ∈ Finset.range (m + 1 - p), a (j + p) * (3 * a j % 5) +
          ∑ j ∈ Finset.range (m + 1 - p), 3 * a (j + p) % 5 * a j := by
        rw [r1, Finset.sum_range_add (fun i => b i * b (i + k)) (3 * m + 2) p, r2,
          Finset.sum_range_add (fun i => b i * b (i + k)) (2 * m + 1 + p) (m + 1 - p),
          Finset.sum_range_add (fun i => b i * b (i + k)) (2 * m + 1) p, r4,
          Finset.sum_range_add (fun i => b i * b (i + k)) (m + 1) m, r5,
          Finset.sum_range_add (fun i => b i * b (i + k)) p (m + 1 - p),
          Finset.sum_eq_zero pa, Finset.sum_congr rfl pb, Finset.sum_eq_zero pc,
          Finset.sum_eq_zero pd, Finset.sum_congr rfl pe, Finset.sum_eq_zero pf]
        simp only [add_zero, zero_add]
      rw [e, Nat.cast_add]
      have qb : ((∑ j ∈ Finset.range (m + 1 - p), a (j + p) * (3 * a j % 5) : ℕ) : ZMod 5) =
          3 * ∑ j ∈ Finset.range (m + 1 - p),
            ((a j : ℕ) : ZMod 5) * ((a (j + p) : ℕ) : ZMod 5) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.cast_mul, ZMod.natCast_mod]
        push_cast
        ring
      have qe : ((∑ j ∈ Finset.range (m + 1 - p), 3 * a (j + p) % 5 * a j : ℕ) : ZMod 5) =
          3 * ∑ j ∈ Finset.range (m + 1 - p),
            ((a j : ℕ) : ZMod 5) * ((a (j + p) : ℕ) : ZMod 5) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.cast_mul, ZMod.natCast_mod]
        push_cast
        ring
      rw [qb, qe, hT p (by omega)]
      linear_combination (r : ZMod 5) * h5
    rcases Nat.lt_or_ge k (3 * m + 2) with c3 | c3
    · -- s <= k < s + n: with p = k - s, two block sums 3 C(p) and 3 C(p)
      obtain ⟨p, hp⟩ : ∃ p, k = 2 * m + 1 + p := ⟨k - (2 * m + 1), by omega⟩
      have pa : ∀ x ∈ Finset.range (m + 1 - p),
          b x * b (x + k) = a x * (3 * a (x + p) % 5) := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbA x (by omega), hbM (x + k) (by omega) (by omega),
          show x + k - (2 * m + 1) = x + p by omega]
      have pb : ∀ x ∈ Finset.range (m + p), b (m + 1 - p + x) * b (m + 1 - p + x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rcases Nat.lt_or_ge (m + 1 - p + x) (m + 1) with h | h
        · rw [hbZ2 (m + 1 - p + x + k) (by omega) (by omega), mul_zero]
        · rw [hbZ1 (m + 1 - p + x) h (by omega), zero_mul]
      have pc : ∀ x ∈ Finset.range (m + 1 - p),
          b (2 * m + 1 + x) * b (2 * m + 1 + x + k) = 3 * a x % 5 * a (x + p) := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbM (2 * m + 1 + x) (by omega) (by omega), hbA2 (2 * m + 1 + x + k) (by omega),
          show 2 * m + 1 + x - (2 * m + 1) = x by omega,
          show 2 * m + 1 + x + k - (4 * m + 2) = x + p by omega]
      have r1 : Finset.range (5 * m + 3 - k) = Finset.range (2 * m + 1 + (m + 1 - p)) :=
        congrArg Finset.range (by omega)
      have r2 : Finset.range (2 * m + 1) = Finset.range (m + 1 - p + (m + p)) :=
        congrArg Finset.range (by omega)
      have e : ∑ i ∈ Finset.range (5 * m + 3 - k), b i * b (i + k) =
          ∑ j ∈ Finset.range (m + 1 - p), a j * (3 * a (j + p) % 5) +
          ∑ j ∈ Finset.range (m + 1 - p), 3 * a j % 5 * a (j + p) := by
        rw [r1, Finset.sum_range_add (fun i => b i * b (i + k)) (2 * m + 1) (m + 1 - p), r2,
          Finset.sum_range_add (fun i => b i * b (i + k)) (m + 1 - p) (m + p),
          Finset.sum_congr rfl pa, Finset.sum_eq_zero pb, Finset.sum_congr rfl pc]
        simp only [add_zero]
      rw [e, Nat.cast_add]
      have qa : ((∑ j ∈ Finset.range (m + 1 - p), a j * (3 * a (j + p) % 5) : ℕ) : ZMod 5) =
          3 * ∑ j ∈ Finset.range (m + 1 - p),
            ((a j : ℕ) : ZMod 5) * ((a (j + p) : ℕ) : ZMod 5) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.cast_mul, ZMod.natCast_mod]
        push_cast
        ring
      have qc : ((∑ j ∈ Finset.range (m + 1 - p), 3 * a j % 5 * a (j + p) : ℕ) : ZMod 5) =
          3 * ∑ j ∈ Finset.range (m + 1 - p),
            ((a j : ℕ) : ZMod 5) * ((a (j + p) : ℕ) : ZMod 5) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.cast_mul, ZMod.natCast_mod]
        push_cast
        ring
      rw [qa, qc, hT p (by omega)]
      linear_combination (r : ZMod 5) * h5
    rcases Nat.lt_or_ge k (4 * m + 2) with c4 | c4
    · -- s + n <= k < 2s: with p = 2s - k, one block sum C(p)
      obtain ⟨p, hp⟩ : ∃ p, k + p = 4 * m + 2 := ⟨4 * m + 2 - k, by omega⟩
      have pa : ∀ x ∈ Finset.range p, b x * b (x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbZ2 (x + k) (by omega) (by omega), mul_zero]
      have pb : ∀ x ∈ Finset.range (m + 1 - p), b (p + x) * b (p + x + k) = a (x + p) * a x := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbA (p + x) (by omega), hbA2 (p + x + k) (by omega),
          show p + x + k - (4 * m + 2) = x by omega, Nat.add_comm p x]
      have pc : ∀ x ∈ Finset.range p, b (m + 1 + x) * b (m + 1 + x + k) = 0 := by
        intro x hx
        have hx' := Finset.mem_range.mp hx
        rw [hbZ1 (m + 1 + x) (by omega) (by omega), zero_mul]
      have r1 : Finset.range (5 * m + 3 - k) = Finset.range (m + 1 + p) :=
        congrArg Finset.range (by omega)
      have r2 : Finset.range (m + 1) = Finset.range (p + (m + 1 - p)) :=
        congrArg Finset.range (by omega)
      have e : ∑ i ∈ Finset.range (5 * m + 3 - k), b i * b (i + k) =
          ∑ j ∈ Finset.range (m + 1 - p), a (j + p) * a j := by
        rw [r1, Finset.sum_range_add (fun i => b i * b (i + k)) (m + 1) p, r2,
          Finset.sum_range_add (fun i => b i * b (i + k)) p (m + 1 - p),
          Finset.sum_eq_zero pa, Finset.sum_congr rfl pb, Finset.sum_eq_zero pc]
        simp only [add_zero, zero_add]
      have q : ((∑ j ∈ Finset.range (m + 1 - p), a (j + p) * a j : ℕ) : ZMod 5) =
          ∑ j ∈ Finset.range (m + 1 - p), ((a j : ℕ) : ZMod 5) * ((a (j + p) : ℕ) : ZMod 5) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.cast_mul]
        ring
      rw [e, q, hT p (by omega)]
    -- 2s <= k: with p = k - 2s, one block sum C(p)
    obtain ⟨p, hp⟩ : ∃ p, k = 4 * m + 2 + p := ⟨k - (4 * m + 2), by omega⟩
    have pa : ∀ x ∈ Finset.range (m + 1 - p), b x * b (x + k) = a x * a (x + p) := by
      intro x hx
      have hx' := Finset.mem_range.mp hx
      rw [hbA x (by omega), hbA2 (x + k) (by omega), show x + k - (4 * m + 2) = x + p by omega]
    have r1 : Finset.range (5 * m + 3 - k) = Finset.range (m + 1 - p) :=
      congrArg Finset.range (by omega)
    have q : ((∑ j ∈ Finset.range (m + 1 - p), a j * a (j + p) : ℕ) : ZMod 5) =
        ∑ j ∈ Finset.range (m + 1 - p), ((a j : ℕ) : ZMod 5) * ((a (j + p) : ℕ) : ZMod 5) := by
      simp only [Nat.cast_sum, Nat.cast_mul]
    rw [r1, Finset.sum_congr rfl pa, q, hT p (by omega)]
