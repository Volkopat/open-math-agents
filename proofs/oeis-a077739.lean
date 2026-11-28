import OMAStatements.S_oeis_a077739

/-!
Choose infinitely many decimal places at which powers of ten have one
fixed residue modulo n. A sum of well-separated blocks 1 and 10 then
has one digit per block, while its residue is the common residue times
the sum of the block values. This constructs a multiple with the exact
digit sum needed between two copies of n.
-/

namespace FramedMultiples

open OMA.S_oeis_a077739

private abbrev ds (n : ℕ) := (Nat.digits 10 n).sum

private theorem append_block (a b k : ℕ) (ha : a < 10 ^ k) :
    ds (a + 10 ^ k * b) = ds a + ds b := by
  by_cases hb : b = 0
  · simp [hb, ds]
  have hl : (Nat.digits 10 a).length ≤ k :=
    (Nat.digits_length_le_iff (by decide : 1 < 10) a).mpr ha
  have h := Nat.digits_append_zeroes_append_digits (b := 10) (n := a)
    (k := k - (Nat.digits 10 a).length) (by decide) (Nat.pos_of_ne_zero hb)
  rw [show (Nat.digits 10 a).length + (k - (Nat.digits 10 a).length) = k by omega] at h
  unfold ds
  rw [← h]
  simp

private theorem multiple_with_digit_sum (n a b : ℕ) (hn : 0 < n) (hd : n ∣ a + 10 * b) :
    ∃ m : ℕ, n ∣ m ∧ ds m = a + b := by
  let : NeZero n := ⟨hn.ne'⟩
  let f (i : ℕ) := (10 : ZMod n) ^ i
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber f
  have make (l : List ℕ) (hl : ∀ d ∈ l, d = 1 ∨ d = 10) :
      ∃ m : ℕ, (m : ZMod n) = r * (l.sum : ℕ) ∧ ds m = l.length := by
    induction l with
    | nil => exact ⟨0, by simp, rfl⟩
    | cons d l ih =>
      obtain ⟨m, hm, hs⟩ := ih (fun j hj => hl j (by simp [hj]))
      obtain ⟨i, hi, him⟩ := (Set.infinite_coe_iff.mp hr).exists_gt m
      have hi' : (10 : ZMod n) ^ i = r := hi
      have hsmall : m < 10 ^ i := him.trans (Nat.lt_pow_self (by decide))
      refine ⟨m + 10 ^ i * d, ?_, ?_⟩
      · simp only [List.sum_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [hi', hm]
        ring
      · have hds : ds d = 1 := by rcases hl d List.mem_cons_self with rfl | rfl <;> decide
        rw [append_block _ _ _ hsmall, hs, hds, List.length_cons]
  let l := List.replicate a 1 ++ List.replicate b 10
  have hblock : ∀ d ∈ l, d = 1 ∨ d = 10 := by
    intro d hd'
    rcases List.mem_append.mp hd' with h | h
    · exact Or.inl (List.eq_of_mem_replicate h)
    · exact Or.inr (List.eq_of_mem_replicate h)
  obtain ⟨m, hm, hs⟩ := make l hblock
  have hsum : l.sum = a + 10 * b := by simp [l, Nat.mul_comm]
  have hz : ((l.sum : ℕ) : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (hsum ▸ hd)
  refine ⟨m, (ZMod.natCast_eq_zero_iff _ _).mp ?_, by simpa [l] using hs⟩
  rw [hm, hz, mul_zero]

private theorem frame (n m : ℕ) (hn : 0 < n) (hm : n ∣ m) (hs : ds m + 2 * ds n = n) :
    ∃ z, qualifies n z := by
  let u := m + 10 ^ (Nat.digits 10 m).length * n
  let z := n + 10 ^ (Nat.digits 10 n).length * u
  have hu : Nat.digits 10 u = Nat.digits 10 m ++ Nat.digits 10 n :=
    (Nat.digits_append_digits (by decide)).symm
  have hz : Nat.digits 10 z =
      Nat.digits 10 n ++ (Nat.digits 10 m ++ Nat.digits 10 n) := by
    rw [← hu]
    exact (Nat.digits_append_digits (by decide)).symm
  have hdu : n ∣ u := dvd_add hm (dvd_mul_left _ _)
  refine ⟨z, (by dsimp [z]; omega), dvd_add (dvd_refl n) (dvd_mul_of_dvd_right hdu _),
    ⟨_, hz.symm⟩, ⟨Nat.digits 10 n ++ Nat.digits 10 m, ?_⟩, ?_⟩
  · simpa only [List.append_assoc] using hz.symm
  · rw [hz, List.sum_append, List.sum_append]
    change ds n + (ds m + ds n) = n
    omega

private theorem digit_sum_step (n : ℕ) (hn : 0 < n) : ds n = n % 10 + ds (n / 10) := by
  exact congrArg List.sum (Nat.digits_of_two_le_of_pos (by decide) hn)

private theorem exists_large (n : ℕ) (hn : 100 ≤ n) : ∃ z, qualifies n z := by
  have h1 := digit_sum_step n (by omega)
  have h2 := digit_sum_step (n / 10) (by omega)
  have h3 : ds (n / 10 / 10) ≤ n / 10 / 10 := Nat.digit_sum_le _ _
  have hbound : 10 * ds n ≤ n := by omega
  have hm := Nat.modEq_digits_sum 9 10 (by decide) n
  change n % 9 = ds n % 9 at hm
  let k := n / 9 - ds n / 9
  have he : n = ds n + 9 * k := by dsimp [k]; omega
  let a := 2 * (k - ds n)
  let b := 7 * k + ds n
  have hab : a + 10 * b = 8 * n := by dsimp [a, b]; omega
  obtain ⟨m, hd, hs⟩ := multiple_with_digit_sum n a b (by omega) (hab ▸ dvd_mul_left _ _)
  apply frame n m (by omega) hd
  dsimp [a, b] at hs
  omega

/-- One witness for each required index below 100. Entries for the exceptional
indices and for zero are unused. Minimality is unnecessary for positivity. -/
private def smallWitnesses : Array ℕ := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
  108010, 11, 122412, 1310413, 1411214, 153015, 16200016, 17, 1818, 19,
  2088020, 2116821, 2217622, 2318423, 244824, 2542525, 2620826, 272727, 2822428, 2923229,
  30699030, 31275931, 32169632, 3375933, 3457834, 3559535, 3628836, 3729637, 3864638, 397839,
  407988040, 411877841, 42499842, 43498843, 44589644, 45499545, 46657846, 4779947, 48196848, 49259749,
  5089995050, 516879951, 527997652, 532999853, 542899854, 559399555, 565588856, 571789857, 581977858, 59896859,
  60499998060, 6159889861, 6259699862, 6319989963, 6438988864, 6548899565, 6634999866, 6716997967, 688989668, 696699969,
  703999989070, 71199999971, 72399988872, 73299978973, 74458999874, 75399997575, 7698898876, 77329998977, 7859989878, 7977988879,
  8049999888080, 811989999981, 822889999882, 831979989983, 84989998884, 85999999585, 86799997886, 87399999987, 881599989688, 89598898889,
  9099999999090, 9149967999991, 9219999999692, 939899998893, 949889899894, 959999899595, 967998988896, 975899898997, 984998989898, 9910989999999]

set_option maxRecDepth 8192 in
private theorem small_correct : ∀ i : Fin 100, 0 < i.val → i.val ≠ 11 → i.val ≠ 17 →
    i.val ≠ 19 → qualifies i.val (smallWitnesses[i.val]?.getD 0) := by
  unfold qualifies
  decide +kernel

private theorem exists_good (n : ℕ) (hn : 0 < n) (h11 : n ≠ 11) (h17 : n ≠ 17)
    (h19 : n ≠ 19) : ∃ m, qualifies n m := by
  by_cases hsmall : n < 100
  · exact ⟨_, small_correct ⟨n, hsmall⟩ hn h11 h17 h19⟩
  · exact exists_large n (by omega)

private theorem alternating_bounds (l : List ℕ) :
    -(l.sum : ℤ) ≤ Nat.ofDigits (-1 : ℤ) l ∧ Nat.ofDigits (-1 : ℤ) l ≤ (l.sum : ℤ) ∧
    Nat.ofDigits (-1 : ℤ) l % 2 = (l.sum : ℤ) % 2 := by
  induction l with
  | nil => decide
  | cons a l ih =>
    simp only [List.sum_cons, Nat.cast_add, Nat.ofDigits, neg_one_mul]
    omega

private theorem no_eleven {m : ℕ} (hm : qualifies 11 m) : False := by
  obtain ⟨_, hdiv, hp, _, hsum⟩ := hm
  change List.IsPrefix [1, 1] (Nat.digits 10 m) at hp
  obtain ⟨tail, ht⟩ := hp
  have hs : tail.sum = 9 := by
    rw [← ht] at hsum
    simp only [List.cons_append, List.nil_append, List.sum_cons] at hsum
    omega
  have hmod := Nat.zmodeq_ofDigits_digits 11 10 (-1) (by decide) m
  have halt : Nat.ofDigits (-1 : ℤ) ([1,1] ++ tail) = Nat.ofDigits (-1 : ℤ) tail := by
    change (1 : ℤ) + (-1) * (1 + (-1) * Nat.ofDigits (-1 : ℤ) tail) = _
    ring
  rw [← ht, halt] at hmod
  change (m : ℤ) % 11 = Nat.ofDigits (-1 : ℤ) tail % 11 at hmod
  have hbound := alternating_bounds tail
  rw [hs] at hbound
  have hd : (11 : ℤ) ∣ (m : ℤ) := by exact_mod_cast hdiv
  omega

/-- Two unequal digits cannot overlap in a three-digit word with the same
two-digit prefix and suffix. -/
private theorem split_ends {a b : ℕ} {L : List ℕ} (hne : a ≠ b)
    (hp : List.IsPrefix [a,b] L) (hs : List.IsSuffix [a,b] L) :
    L = [a,b] ∨ ∃ w, L = [a,b] ++ (w ++ [a,b]) := by
  obtain ⟨tail, rfl⟩ := hp
  obtain ⟨front, hf⟩ := hs
  cases front with
  | nil => exact Or.inl hf.symm
  | cons p front =>
    cases front with
    | nil => exact False.elim (hne (List.cons.inj (List.cons.inj hf).2).1)
    | cons q mid =>
      have ht : mid ++ [a,b] = tail := (List.cons.inj (List.cons.inj hf).2).2
      exact Or.inr ⟨mid, by rw [ht]⟩

private theorem no_nineteen {m : ℕ} (hm : qualifies 19 m) : False := by
  obtain ⟨_, _, hp, hs, hsum⟩ := hm
  change List.IsPrefix [9,1] (Nat.digits 10 m) at hp
  change List.IsSuffix [9,1] (Nat.digits 10 m) at hs
  rcases split_ends (by decide) hp hs with h | ⟨w, h⟩
  · rw [h] at hsum
    change 10 = 19 at hsum
    omega
  · rw [h] at hsum
    simp at hsum
    omega

private theorem value_zero (l : List ℕ) (h : l.sum = 0) : Nat.ofDigits 10 l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.sum_cons] at h
    obtain ⟨rfl, hl⟩ := Nat.add_eq_zero_iff.mp h
    simp [Nat.ofDigits_cons, ih hl]

private theorem value_one (l : List ℕ) (h : l.sum = 1) :
    ∃ e : ℕ, Nat.ofDigits 10 l = 10 ^ e := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons] at h
    by_cases ha : a = 0
    · obtain ⟨e, he⟩ := ih (by omega)
      exact ⟨e + 1, by simp [Nat.ofDigits_cons, ha, he, pow_succ']⟩
    · exact ⟨0, by rw [Nat.ofDigits_cons, value_zero l (by omega)]; omega⟩

private theorem no_seventeen {m : ℕ} (hm : qualifies 17 m) : False := by
  obtain ⟨_, hdiv, hp, hs, hsum⟩ := hm
  change List.IsPrefix [7,1] (Nat.digits 10 m) at hp
  change List.IsSuffix [7,1] (Nat.digits 10 m) at hs
  rcases split_ends (by decide) hp hs with h | ⟨w, h⟩
  · rw [h] at hsum
    change 8 = 17 at hsum
    omega
  · have hw : w.sum = 1 := by
      rw [h] at hsum
      simp at hsum
      omega
    obtain ⟨e, he⟩ := value_one w hw
    have hv : m = 17 + 100 * (10 ^ e + 10 ^ w.length * 17) := calc
      _ = Nat.ofDigits 10 (Nat.digits 10 m) := (Nat.ofDigits_digits 10 m).symm
      _ = _ := by
        rw [h, Nat.ofDigits_append, Nat.ofDigits_append]
        change 17 + 100 * (Nat.ofDigits 10 w + 10 ^ w.length * 17) = _
        rw [he]
    have hd : 17 ∣ 100 * 10 ^ e := by omega
    have hd' : 17 ∣ 10 ^ e := (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 17 100)).mp hd
    exact (by decide : ¬ (17 : ℕ) ∣ 10) ((by decide : Nat.Prime 17).dvd_of_dvd_pow hd')

theorem classification (n : ℕ) (hn : 0 < n) :
    term n = 0 ↔ n = 11 ∨ n = 17 ∨ n = 19 := by
  constructor
  · intro h
    by_contra! he
    obtain ⟨m, hm⟩ := exists_good n hn he.1 he.2.1 he.2.2
    have hex : {z | qualifies n z}.Nonempty := ⟨m, hm⟩
    have hq : qualifies n (term n) := Nat.sInf_mem hex
    exact (Nat.ne_of_gt hq.1) h
  · intro he
    have hempty : {z | qualifies n z} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      rcases he with rfl | rfl | rfl
      · exact no_eleven hz
      · exact no_seventeen hz
      · exact no_nineteen hz
    simp [term, hempty]

end FramedMultiples

theorem OMA.solution : type_of% @OMA.S_oeis_a077739.main := FramedMultiples.classification
