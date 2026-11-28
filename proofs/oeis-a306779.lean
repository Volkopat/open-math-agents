import OMAStatements.S_oeis_a306779

-- Problem: A306779: Table read by rows: T(n,k) is the length of the longest non-intersecting loop starting at (0,0) on the n X k torus consisting of steps up and to the right, 1 <= k <= n.
-- Upstream: formal-conjectures statements/oeis-a306779.lean:0 (declaration OMA.S_oeis_a306779.main)
-- Credit: @thtsben2 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a306779

open OMA.S_oeis_a306779

private lemma eastCount_zero (w : ℕ → Bool) : eastCount w 0 = 0 := by
  simp [eastCount]

private lemma eastCount_succ (w : ℕ → Bool) (i : ℕ) :
    eastCount w (i + 1) = eastCount w i + if w i = true then 1 else 0 := by
  unfold eastCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · have hmem : i ∉ (Finset.range i).filter (fun j => w j = true) := by
      simp [Finset.mem_filter, Finset.mem_range]
    rw [Finset.card_insert_of_notMem hmem]
  · simp

private lemma eastCount_le (w : ℕ → Bool) (i : ℕ) : eastCount w i ≤ i := by
  unfold eastCount
  exact (Finset.card_filter_le _ _).trans (by simp)

private lemma eastCount_add (w : ℕ → Bool) (a b : ℕ) :
    eastCount w (a + b) =
      eastCount w a + ((Finset.range b).filter fun r => w (a + r) = true).card := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, eastCount_succ, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · have hmem : b ∉ (Finset.range b).filter (fun r => w (a + r) = true) := by
        simp [Finset.mem_filter, Finset.mem_range]
      rw [Finset.card_insert_of_notMem hmem]
      omega
    · omega

private lemma pos_fst_lt (w : ℕ → Bool) (i : ℕ) : (pos 4368 880 w i).1 < 4368 :=
  Nat.mod_lt _ (by positivity)

private lemma pos_snd_lt (w : ℕ → Bool) (i : ℕ) : (pos 4368 880 w i).2 < 880 :=
  Nat.mod_lt _ (by positivity)

private def step (b : Bool) (p : ℕ × ℕ) : ℕ × ℕ :=
  if b then ((p.1 + 1) % 4368, p.2) else (p.1, (p.2 + 1) % 880)

private lemma pos_succ (w : ℕ → Bool) (i : ℕ) :
    pos 4368 880 w (i + 1) = step (w i) (pos 4368 880 w i) := by
  have hle := eastCount_le w i
  unfold pos step
  rw [eastCount_succ]
  cases h : w i
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    congr 1
    rw [show i + 1 - eastCount w i = (i - eastCount w i) + 1 by omega, Nat.mod_add_mod]
  · simp only [↓reduceIte]
    congr 1
    · rw [Nat.mod_add_mod]
    · rw [show i + 1 - (eastCount w i + 1) = i - eastCount w i by omega]

private def shift (p : ℕ × ℕ) : ℕ × ℕ :=
  ((p.1 + 1) % 4368, (p.2 + 879) % 880)

private lemma shift_iterate (p : ℕ × ℕ) (hp1 : p.1 < 4368) (hp2 : p.2 < 880) (t : ℕ) :
    shift^[t] p = ((p.1 + t) % 4368, (p.2 + 879 * t) % 880) := by
  induction t with
  | zero =>
    simp [Function.iterate_zero, Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2]
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    dsimp [shift]
    refine Prod.ext ?_ ?_ <;> dsimp only
    · rw [Nat.mod_add_mod, show p.1 + t + 1 = p.1 + (t + 1) by ring]
    · rw [Nat.mod_add_mod, show p.2 + 879 * t + 879 = p.2 + 879 * (t + 1) by ring]

private lemma mod_add_4368 (x y : ℕ) (hx : x < 4368) (hy : y < 4368) :
    (x + (y + 4368 - x) % 4368) % 4368 = y := by
  rcases le_or_gt x y with hle | hgt
  · have hu : (y + 4368 - x) % 4368 = y - x := by
      rw [show y + 4368 - x = (y - x) + 4368 * 1 by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hu, show x + (y - x) = y by omega]
    exact Nat.mod_eq_of_lt hy
  · have hu : (y + 4368 - x) % 4368 = y + 4368 - x := Nat.mod_eq_of_lt (by omega)
    rw [hu, show x + (y + 4368 - x) = y + 4368 * 1 by omega,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hy

private lemma mod_sub_879_880 (x y : ℕ) (hx : x < 880) (hy : y < 880) :
    (x + 879 * ((x + 880 - y) % 880)) % 880 = y := by
  rcases le_or_gt y x with hle | hgt
  · have hv : (x + 880 - y) % 880 = x - y := by
      rw [show x + 880 - y = (x - y) + 880 * 1 by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hv, show x + 879 * (x - y) = y + 880 * (x - y) by omega,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hy
  · have hv : (x + 880 - y) % 880 = x + 880 - y := Nat.mod_eq_of_lt (by omega)
    rw [hv, show x + 879 * (x + 880 - y) = y + 880 * (x + 879 - y) by omega,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hy

private lemma crt_4368_880 (u v : ℕ) (hu : u < 4368) (hv : v < 880)
    (h16 : u % 16 = v % 16) :
    ∃ t : ℕ, t % 4368 = u ∧ t % 880 = v := by
  let d : ℕ := (v + 880 - u % 880) % 880
  have hd_lt : d < 880 := Nat.mod_lt _ (by positivity)
  have hd16 : d % 16 = 0 := by
    have h1 : d % 16 = (v + 880 - u % 880) % 16 :=
      Nat.mod_mod_of_dvd _ (by norm_num : 16 ∣ 880)
    have h2 : (u % 880) % 16 = u % 16 :=
      Nat.mod_mod_of_dvd _ (by norm_num : 16 ∣ 880)
    have hum : u % 880 < 880 := Nat.mod_lt _ (by positivity)
    dsimp [d] at h1 ⊢
    omega
  have hq_lt : d / 16 < 55 := by omega
  have hd_eq : 16 * (d / 16) = d := by omega
  let m : ℕ := (27 * (d / 16)) % 55
  refine ⟨m * 4368 + u, ?_, ?_⟩
  · rw [add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hu
  · have hm_mod : (m * 4368) % 880 = d := by
      rw [show 4368 = 16 * 273 by norm_num, show 880 = 16 * 55 by norm_num,
        show m * (16 * 273) = 16 * (m * 273) by ring, Nat.mul_mod_mul_left]
      have h273 : (m * 273) % 55 = d / 16 := by
        dsimp [m]
        rw [Nat.mod_mul_mod, show 27 * (d / 16) * 273 = (d / 16) + 55 * (134 * (d / 16)) by ring,
          Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hq_lt
      rw [h273, hd_eq]
    rw [Nat.add_mod, hm_mod]
    have hum : u % 880 < 880 := Nat.mod_lt _ (by positivity)
    rcases le_or_gt (u % 880) v with hle | hgt
    · have hd_val : d = v - u % 880 := by
        dsimp [d]
        rw [show v + 880 - u % 880 = (v - u % 880) + 880 * 1 by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hd_val, show v - u % 880 + u % 880 = v by omega]
      exact Nat.mod_eq_of_lt hv
    · have hd_val : d = v + 880 - u % 880 := Nat.mod_eq_of_lt (by omega)
      rw [hd_val, show v + 880 - u % 880 + u % 880 = v + 880 * 1 by omega,
        Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hv

private lemma shift_connect (p q : ℕ × ℕ)
    (hp1 : p.1 < 4368) (hp2 : p.2 < 880) (hq1 : q.1 < 4368) (hq2 : q.2 < 880)
    (hdiag : (p.1 + p.2) % 16 = (q.1 + q.2) % 16) :
    ∃ t : ℕ, shift^[t] p = q := by
  let u : ℕ := (q.1 + 4368 - p.1) % 4368
  let v : ℕ := (p.2 + 880 - q.2) % 880
  have hu16 : u % 16 = (q.1 + 4368 - p.1) % 16 :=
    Nat.mod_mod_of_dvd _ (by norm_num : 16 ∣ 4368)
  have hv16 : v % 16 = (p.2 + 880 - q.2) % 16 :=
    Nat.mod_mod_of_dvd _ (by norm_num : 16 ∣ 880)
  have h16 : u % 16 = v % 16 := by omega
  obtain ⟨t, ht1, ht2⟩ :=
    crt_4368_880 u v (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)) h16
  refine ⟨t, ?_⟩
  rw [shift_iterate p hp1 hp2 t]
  refine Prod.ext ?_ ?_ <;> dsimp only
  · rw [← Nat.add_mod_mod, ht1]
    exact mod_add_4368 p.1 q.1 hp1 hq1
  · rw [← Nat.add_mod_mod, Nat.mul_mod 879 t 880, ht2, Nat.mod_mul_mod, Nat.add_mod_mod]
    exact mod_sub_879_880 p.2 q.2 hp2 hq2

private lemma pos_diag_mod (w : ℕ → Bool) (i : ℕ) :
    ((pos 4368 880 w i).1 + (pos 4368 880 w i).2) % 16 = i % 16 := by
  have hle := eastCount_le w i
  unfold pos
  have h1 : (eastCount w i % 4368) % 16 = eastCount w i % 16 :=
    Nat.mod_mod_of_dvd _ (by norm_num : 16 ∣ 4368)
  have h2 : ((i - eastCount w i) % 880) % 16 = (i - eastCount w i) % 16 :=
    Nat.mod_mod_of_dvd _ (by norm_num : 16 ∣ 880)
  omega

private lemma succ_mod_inj {i j M : ℕ} (hi : i < M) (hj : j < M)
    (h : (i + 1) % M = (j + 1) % M) : i = j := by
  rcases Nat.lt_or_eq_of_le (show i + 1 ≤ M by omega) with hi1 | hi1 <;>
    rcases Nat.lt_or_eq_of_le (show j + 1 ≤ M by omega) with hj1 | hj1
  · rw [Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj1] at h
    omega
  · rw [Nat.mod_eq_of_lt hi1, hj1, Nat.mod_self] at h
    omega
  · rw [hi1, Nat.mod_self, Nat.mod_eq_of_lt hj1] at h
    omega
  · omega

private lemma no_full_loop_4368_880 : ¬ HasFullLoop 4368 880 := by
  rintro ⟨w, hclose, hinj⟩
  let N : ℕ := 4368 * 880
  have hpos_mod : ∀ m : ℕ, m ≤ N → pos 4368 880 w (m % N) = pos 4368 880 w m := by
    intro m hm
    rcases lt_or_eq_of_le hm with hlt | rfl
    · rw [Nat.mod_eq_of_lt hlt]
    · rw [Nat.mod_self]
      dsimp [N]
      rw [hclose]
      simp [pos, eastCount_zero]
  let F : Fin N → Fin 4368 × Fin 880 := fun i =>
    (⟨(pos 4368 880 w i.1).1, pos_fst_lt w i.1⟩,
      ⟨(pos 4368 880 w i.1).2, pos_snd_lt w i.1⟩)
  have hFinj : Function.Injective F := by
    intro i j hij
    have h1 : (pos 4368 880 w i.1).1 = (pos 4368 880 w j.1).1 :=
      congrArg (fun x => x.1.1) hij
    have h2 : (pos 4368 880 w i.1).2 = (pos 4368 880 w j.1).2 :=
      congrArg (fun x => x.2.1) hij
    have hp : pos 4368 880 w i.1 = pos 4368 880 w j.1 := Prod.ext h1 h2
    exact Fin.ext (hinj i.isLt j.isLt hp)
  have hFsurj : Function.Surjective F :=
    (Fintype.bijective_iff_injective_and_card F).mpr ⟨hFinj, by simp [N]⟩ |>.2
  have hsurj : ∀ p : ℕ × ℕ, p.1 < 4368 → p.2 < 880 → ∃ i < N, pos 4368 880 w i = p := by
    intro p hp1 hp2
    obtain ⟨i, hi⟩ := hFsurj (⟨p.1, hp1⟩, ⟨p.2, hp2⟩)
    refine ⟨i.1, i.isLt, Prod.ext ?_ ?_⟩
    · exact congrArg (fun x => x.1.1) hi
    · exact congrArg (fun x => x.2.1) hi
  have hforce : ∀ i j : ℕ, i < N → j < N →
      pos 4368 880 w j = shift (pos 4368 880 w i) → w i = true → w j = true := by
    intro i j hi hj hsh hwi
    by_contra hwj
    have hwj' : w j = false := Bool.eq_false_iff.mpr hwj
    have h1 : pos 4368 880 w ((i + 1) % N) = pos 4368 880 w (i + 1) :=
      hpos_mod (i + 1) (Nat.succ_le_of_lt hi)
    have h2 : pos 4368 880 w ((j + 1) % N) = pos 4368 880 w (j + 1) :=
      hpos_mod (j + 1) (Nat.succ_le_of_lt hj)
    rw [pos_succ, hwi] at h1
    rw [pos_succ, hwj', hsh] at h2
    dsimp [step, shift] at h1 h2
    have hsnd := pos_snd_lt w i
    have hsnd_eq : (((pos 4368 880 w i).2 + 879) % 880 + 1) % 880 = (pos 4368 880 w i).2 := by
      rw [Nat.mod_add_mod, show (pos 4368 880 w i).2 + 879 + 1 = (pos 4368 880 w i).2 + 880 * 1 by ring,
        Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hsnd
    have hstep_eq : pos 4368 880 w ((i + 1) % N) = pos 4368 880 w ((j + 1) % N) := by
      rw [h1, h2, hsnd_eq]
    have hij_mod : (i + 1) % N = (j + 1) % N :=
      hinj (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)) hstep_eq
    have hij : i = j := succ_mod_inj hi hj hij_mod
    subst hij
    have hfst := pos_fst_lt w i
    have hxf : (pos 4368 880 w i).1 = ((pos 4368 880 w i).1 + 1) % 4368 :=
      congrArg Prod.fst hsh
    omega
  have hiter_true : ∀ t i : ℕ, i < N → w i = true →
      ∃ j < N, pos 4368 880 w j = shift^[t] (pos 4368 880 w i) ∧ w j = true := by
    intro t
    induction t with
    | zero =>
      intro i hi hwi
      exact ⟨i, hi, rfl, hwi⟩
    | succ t ih =>
      intro i hi hwi
      obtain ⟨j, hj, hposj, hwj⟩ := ih i hi hwi
      obtain ⟨j', hj', hposj'⟩ := hsurj (shift (pos 4368 880 w j))
        (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
      have hwj' := hforce j j' hj hj' hposj' hwj
      refine ⟨j', hj', ?_, hwj'⟩
      rw [Function.iterate_succ_apply', hposj', hposj]
  have hper_imp : ∀ i j : ℕ, i < N → j < N → i % 16 = j % 16 → w i = true → w j = true := by
    intro i j hi hj hmod hwi
    have hdiag : ((pos 4368 880 w i).1 + (pos 4368 880 w i).2) % 16 =
        ((pos 4368 880 w j).1 + (pos 4368 880 w j).2) % 16 := by
      rw [pos_diag_mod, pos_diag_mod, hmod]
    obtain ⟨t, ht⟩ := shift_connect (pos 4368 880 w i) (pos 4368 880 w j)
      (pos_fst_lt w i) (pos_snd_lt w i) (pos_fst_lt w j) (pos_snd_lt w j) hdiag
    obtain ⟨j', hj', hposj', hwj'⟩ := hiter_true t i hi hwi
    rw [ht] at hposj'
    have hjj' : j' = j := hinj hj' hj hposj'
    rwa [← hjj']
  have hper : ∀ i j : ℕ, i < N → j < N → i % 16 = j % 16 → w i = w j := by
    intro i j hi hj hmod
    cases hwi : w i <;> cases hwj : w j
    · rfl
    · exact absurd (hper_imp j i hj hi hmod.symm hwj) (by simp [hwi])
    · exact absurd (hper_imp i j hi hj hmod hwi) (by simp [hwj])
    · rfl
  let d1 : ℕ := eastCount w 16
  have hd1_le : d1 ≤ 16 := eastCount_le w 16
  have heast_mul : ∀ m : ℕ, 16 * m ≤ N → eastCount w (16 * m) = m * d1 := by
    intro m hm
    induction m with
    | zero => simp [eastCount_zero]
    | succ m ih =>
      rw [show 16 * (m + 1) = 16 * m + 16 by ring, eastCount_add, ih (by omega)]
      have hfil : ((Finset.range 16).filter fun r => w (16 * m + r) = true) =
          (Finset.range 16).filter fun r => w r = true := by
        refine Finset.filter_congr fun r hr => ?_
        have hr16 : r < 16 := Finset.mem_range.mp hr
        have h1 : 16 * m + r < N := by omega
        have h2 : r < N := by dsimp [N]; omega
        have hmod : (16 * m + r) % 16 = r % 16 := by rw [Nat.mul_add_mod]
        rw [hper (16 * m + r) r h1 h2 hmod]
      rw [hfil]
      change m * d1 + d1 = (m + 1) * d1
      ring
  have hm_ex : ∃ m : ℕ, 0 < 16 * m ∧ 16 * m < N ∧
      (m * d1) % 4368 = 0 ∧ (16 * m - m * d1) % 880 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one d1 with hd_even | hd_odd
    · refine ⟨120120, by norm_num, by norm_num [N], ?_, ?_⟩
      · obtain ⟨q, hq⟩ : ∃ q, d1 = 2 * q := ⟨d1 / 2, by omega⟩
        rw [hq, show 120120 * (2 * q) = 4368 * (55 * q) by ring, Nat.mul_mod_right]
      · obtain ⟨q, hq⟩ : ∃ q, d1 = 2 * q := ⟨d1 / 2, by omega⟩
        have hq8 : q ≤ 8 := by omega
        rw [hq, show 16 * 120120 - 120120 * (2 * q) = 880 * (273 * (8 - q)) by omega,
          Nat.mul_mod_right]
    · have hd_cases : d1 = 1 ∨ d1 = 3 ∨ d1 = 5 ∨ d1 = 7 ∨
          d1 = 9 ∨ d1 = 11 ∨ d1 = 13 ∨ d1 = 15 := by omega
      rcases hd_cases with h | h | h | h | h | h | h | h <;> rw [h]
      · exact ⟨48048, by norm_num, by norm_num [N], by norm_num, by norm_num⟩
      · exact ⟨80080, by norm_num, by norm_num [N], by norm_num, by norm_num⟩
      · exact ⟨21840, by norm_num, by norm_num [N], by norm_num, by norm_num⟩
      · exact ⟨34320, by norm_num, by norm_num [N], by norm_num, by norm_num⟩
      · exact ⟨80080, by norm_num, by norm_num [N], by norm_num, by norm_num⟩
      · exact ⟨48048, by norm_num, by norm_num [N], by norm_num, by norm_num⟩
      · exact ⟨18480, by norm_num, by norm_num [N], by norm_num, by norm_num⟩
      · exact ⟨80080, by norm_num, by norm_num [N], by norm_num, by norm_num⟩
  obtain ⟨m, hm_pos, hm_lt, hm_x, hm_y⟩ := hm_ex
  have hpos_m : pos 4368 880 w (16 * m) = (0, 0) := by
    unfold pos
    rw [heast_mul m hm_lt.le, hm_x, hm_y]
  have hpos_0 : pos 4368 880 w 0 = (0, 0) := by
    simp [pos, eastCount_zero]
  have heq : 16 * m = 0 := hinj hm_lt (by dsimp [N]; norm_num) (hpos_m.trans hpos_0.symm)
  omega

end OMA.Proof_oeis_a306779

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a306779.main) := by
  intro h
  have h1 := (h 4368 880 (by norm_num) (by norm_num)).mpr (Or.inr (by norm_num))
  exact OMA.Proof_oeis_a306779.no_full_loop_4368_880 h1
