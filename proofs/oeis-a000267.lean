import OMAStatements.S_oeis_a000267

namespace A000267

open OMA.S_oeis_a000267

private abbrev parts (first : ℕ) (rest : List ℕ) : List ℕ :=
  rest.scanl (fun part run => part + (run - 1)) first

private theorem parts_bound (rest : List ℕ) (first : ℕ) :
    (parts first rest).sum ≤ (rest.length + 1) * (first + (rest.map (· - 1)).sum) := by
  induction rest generalizing first with
  | nil => simp
  | cons run rest ih =>
    have bound := ih (first + (run - 1))
    simp only [parts, List.scanl_cons, List.sum_cons, List.length_cons, List.map_cons] at *
    let top := first + (run - 1 + (rest.map (· - 1)).sum)
    change first + _ ≤ (rest.length + 1 + 1) * top
    rw [Nat.add_mul (rest.length + 1) 1 top, Nat.one_mul, Nat.add_comm _ top]
    exact Nat.add_le_add (by dsimp [top]; omega) (by simpa only [top, Nat.add_assoc] using bound)

private theorem increments_sum (runs : List ℕ) (h : ∀ x ∈ runs, 0 < x) :
    (runs.map (· - 1)).sum + runs.length = runs.sum := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
    have hr := h run (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem weight_bound (code : ℕ) :
    4 * partitionWeight code ≤ (code.log2 + 2)^2 := by
  by_cases hz : code = 0
  · simp [hz, partitionWeight]
  let bits := (List.range (code.log2 + 1)).map code.testBit
  let groups := bits.splitBy (· == ·)
  have hsum : (groups.map List.length).sum = code.log2 + 1 := by
    rw [← List.length_flatten, show groups.flatten = bits from List.flatten_splitBy _ _]
    simp [bits]
  have hpos (x : ℕ) (hx : x ∈ groups.map List.length) : 0 < x := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact List.length_pos_iff.mpr (List.ne_nil_of_mem_splitBy hg)
  unfold partitionWeight
  rw [if_neg hz]
  change 4 * (match groups.map List.length with
    | [] => 0
    | first :: rest => (parts first rest).sum) ≤ _
  cases hruns : groups.map List.length with
  | nil => simp
  | cons first rest =>
    have hinc := increments_sum rest (fun x hx => hpos x (by simp [hruns, hx]))
    have htotal : (rest.length + 1) + (first + (rest.map (· - 1)).sum) = code.log2 + 2 := by
      rw [hruns, List.sum_cons] at hsum
      omega
    let tail := (rest.map (· - 1)).sum
    have h : (parts first rest).sum ≤ (rest.length + 1) * (first + tail) :=
      parts_bound rest first
    rw [← htotal]
    change 4 * (parts first rest).sum ≤ (rest.length + 1 + (first + tail))^2
    zify at h ⊢
    nlinarith [sq_nonneg ((rest.length : ℤ) + 1 - ((first : ℤ) + (tail : ℤ)))]

private def runBit : List ℕ → Bool
  | [] => false
  | _ :: rest => !runBit rest

private def runGroups : List ℕ → List (List Bool)
  | [] => []
  | run :: rest => List.replicate run (runBit (run :: rest)) :: runGroups rest

private theorem runGroups_lengths (runs : List ℕ) :
    (runGroups runs).map List.length = runs := by
  induction runs with
  | nil => rfl
  | cons run rest ih => simp [runGroups, ih]

private theorem runGroups_length (runs : List ℕ) : (runGroups runs).flatten.length = runs.sum := by
  rw [List.length_flatten, runGroups_lengths]

private theorem runGroups_last (runs : List ℕ) (h : ∀ x ∈ runs, 0 < x) (hne : runs ≠ []) :
    (runGroups runs).flatten.getLast? = some true := by
  induction runs with
  | nil => contradiction
  | cons run rest ih =>
    have hr := h run (by simp)
    cases rest with
    | nil =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : run ≠ 0)
      simp [runGroups, runBit, List.getLast?_replicate]
    | cons next rest =>
      have ht := ih (fun x hx => h x (by simp [hx])) (by simp)
      change (List.replicate run (runBit (run :: next :: rest)) ++
        (runGroups (next :: rest)).flatten).getLast? = some true
      rw [List.getLast?_append, ht]
      rfl

private theorem split_runGroups (runs : List ℕ) (h : ∀ x ∈ runs, 0 < x) :
    (runGroups runs).flatten.splitBy (· == ·) = runGroups runs := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    have hr := h run (by simp)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : run ≠ 0)
    have hs : (List.replicate (k + 1) (runBit ((k + 1) :: rest))).splitBy (· == ·) =
        [List.replicate (k + 1) (runBit ((k + 1) :: rest))] := by
      apply List.splitBy_of_isChain
      · simp
      · exact List.isChain_replicate_of_rel _ (by simp)
    simp only [runGroups, List.flatten_cons]
    rw [List.splitBy_append, hs, ih (fun x hx => h x (by simp [hx]))]
    · rfl
    · intro x hx y hy
      have hx' : x = runBit ((k + 1) :: rest) := by
        simpa [List.getLast?_replicate, eq_comm] using hx
      cases rest with
      | nil => simp [runGroups] at hy
      | cons next rest =>
        have hn := h next (by simp)
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : next ≠ 0)
        have hy' : y = runBit ((j + 1) :: rest) := by
          simpa [runGroups, List.replicate_succ, eq_comm] using hy
        rw [hx', hy', runBit]
        cases runBit ((j + 1) :: rest) <;> rfl

private theorem bits_code (bits : List Bool) (h : bits.getLast? = some true) :
    ∃ code : ℕ, code ≠ 0 ∧ code.bits = bits ∧ code.log2 + 1 = bits.length := by
  induction bits with
  | nil => simp at h
  | cons bit rest ih =>
    cases rest with
    | nil =>
      have hb : bit = true := by simpa using h
      subst bit
      exact ⟨1, by decide, Nat.one_bits, by decide⟩
    | cons next rest =>
      obtain ⟨code, hc, hbits, hlen⟩ := ih (by simpa using h)
      refine ⟨Nat.bit bit code, Nat.bit_ne_zero _ hc, ?_, ?_⟩
      · rw [Nat.bits_append_bit _ _ (fun hz => (hc hz).elim), hbits]
      · have hd : Nat.bit bit code / 2 = code := by
          rw [← Nat.div2_val, Nat.div2_bit]
        have hg : 2 ≤ Nat.bit bit code := by omega
        simp only [Nat.log2_def (Nat.bit bit code), if_pos hg, hd, List.length_cons] at *
        omega

private theorem bits_from_range (code : ℕ) (hlen : code.log2 + 1 = code.bits.length) :
    (List.range (code.log2 + 1)).map code.testBit = code.bits := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    rw [List.getElem_map, List.getElem_range, Nat.testBit_eq_inth, List.getI_eq_getElem _ hj]

private theorem code_for_runs (first : ℕ) (rest : List ℕ)
    (h : ∀ x ∈ first :: rest, 0 < x) :
    ∃ code : ℕ, partitionWeight code = (parts first rest).sum ∧
      code.log2 + 1 = first + rest.sum := by
  let runs := first :: rest
  obtain ⟨code, hc, hb, hl⟩ := bits_code (runGroups runs).flatten (runGroups_last runs h (by simp [runs]))
  have hbits := bits_from_range code (by rw [hb]; exact hl)
  rw [hb] at hbits
  refine ⟨code, ?_, ?_⟩
  · simp only [partitionWeight, if_neg hc, hbits, split_runGroups runs h, runGroups_lengths]
    rfl
  · rw [hl, runGroups_length]
    rfl

private theorem parts_ones (first count : ℕ) :
    (parts first (List.replicate count 1)).sum = (count + 1) * first := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [List.replicate_succ, parts, List.scanl_cons, Nat.sub_self, Nat.add_zero, List.sum_cons] at *
    rw [ih]
    ring

private theorem balanced_bounds (n L r w : ℕ)
    (hL : L = Nat.sqrt (4 * n + 1)) (hr : r = (L + 1) / 2) (hw : w = L + 1 - r) :
    (r - 1) * w < n + 1 ∧ n + 1 ≤ r * w := by
  have hlo : L * L ≤ 4 * n + 1 := hL ▸ Nat.sqrt_le _
  have hhi : 4 * n + 1 < (L + 1) * (L + 1) := hL ▸ Nat.lt_succ_sqrt _
  have hpos : 1 ≤ L := by
    rw [hL]
    exact Nat.le_sqrt.mpr (by omega)
  have hsides : w = r ∨ w = r + 1 := by omega
  have hsmall : 4 * ((r - 1) * w) ≤ L * L := by
    rcases hsides with hs | hs
    · have h : 2 * (r - 1) + 1 = L := by omega
      have hw' : w = (r - 1) + 1 := by omega
      rw [← h, hw']
      nlinarith
    · have h : 2 * (r - 1) + 2 = L := by omega
      have hw' : w = (r - 1) + 2 := by omega
      rw [← h, hw']
      nlinarith
  have hlarge : (L + 1) * (L + 1) ≤ 4 * (r * w) + 1 := by
    rcases hsides with hs | hs
    · have h : L + 1 = 2 * r := by omega
      rw [h, hs]
      nlinarith
    · have h : L + 1 = 2 * r + 1 := by omega
      rw [h, hs]
      nlinarith
  omega

private theorem witness (n : ℕ) :
    ∃ code, partitionWeight code = n + 1 ∧ code.log2 + 1 = Nat.sqrt (4 * n + 1) := by
  let L := Nat.sqrt (4 * n + 1)
  let r := (L + 1) / 2
  let w := L + 1 - r
  have hL : 1 ≤ L := Nat.le_sqrt.mpr (by omega)
  have hr : r = (L + 1) / 2 := rfl
  have hw : w = L + 1 - r := rfl
  have hrpos : 1 ≤ r := by omega
  have hwpos : 1 ≤ w := by omega
  obtain ⟨hlo, hhi⟩ := balanced_bounds n L r w rfl hr hw
  let t := n + 1 - (r - 1) * w
  have harea : (r - 1) * w + w = r * w := by
    calc
      (r - 1) * w + w = (r - 1 + 1) * w := by rw [Nat.add_mul, Nat.one_mul]
      _ = r * w := by rw [show r - 1 + 1 = r by omega]
  have htpos : 0 < t := by dsimp [t]; omega
  have htw : t ≤ w := by dsimp [t]; omega
  by_cases heq : t = w
  · obtain ⟨code, hweight, hlen⟩ := code_for_runs w (List.replicate (r - 1) 1) (by
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨_, rfl⟩ <;> omega)
    rw [parts_ones, show r - 1 + 1 = r by omega] at hweight
    simp at hlen
    exact ⟨code, by dsimp [t] at heq; omega, by omega⟩
  · have hr2 : 2 ≤ r := by
      by_contra! hn
      have hr1 : r = 1 := by omega
      have hLn : L * L ≤ 4 * n + 1 := Nat.sqrt_le _
      have hL12 : L = 1 ∨ L = 2 := by omega
      have htn : t = n + 1 := by simp [t, hr1]
      rcases hL12 with hh | hh
      · omega
      · rw [hh] at hLn
        omega
    obtain ⟨code, hweight, hlen⟩ :=
      code_for_runs t ((w - t + 1) :: List.replicate (r - 2) 1) (by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl | ⟨_, rfl⟩ <;> omega)
    simp only [parts, List.scanl_cons, List.sum_cons, Nat.add_sub_cancel] at hweight
    change partitionWeight code =
      t + (parts (t + (w - t)) (List.replicate (r - 2) 1)).sum at hweight
    rw [show t + (w - t) = w by omega, parts_ones, show r - 2 + 1 = r - 1 by omega] at hweight
    simp at hlen
    exact ⟨code, by dsimp [t] at hweight ⊢; omega, by omega⟩

end A000267

theorem OMA.solution : type_of% @OMA.S_oeis_a000267.main := by
  intro n
  classical
  obtain ⟨code, hcode, hlen⟩ := A000267.witness n
  have hex : ∃ k, OMA.S_oeis_a000267.partitionWeight k = n + 1 := ⟨code, hcode⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk, ?_⟩
  have hupper : (Nat.find hex).log2 ≤ code.log2 := by
    have hle := Nat.find_min' hex hcode
    by_cases hz : Nat.find hex = 0
    · simp [hz]
    · exact (Nat.le_log2 (by omega)).2 (le_trans (Nat.log2_self_le hz) hle)
  have hweight := A000267.weight_bound (Nat.find hex)
  rw [Nat.find_spec hex] at hweight
  have hlower : Nat.sqrt (4 * n + 1) ≤ (Nat.find hex).log2 + 1 := by
    by_contra! h
    have hsq : ((Nat.find hex).log2 + 2)^2 ≤ (Nat.sqrt (4 * n + 1))^2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hs := Nat.sqrt_le (4 * n + 1)
    rw [← pow_two] at hs
    omega
  omega
