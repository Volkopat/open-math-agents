import OMAStatements.S_oeis_a133901

namespace OMA.S_oeis_a133901

private def spaced (k : ℕ) (blocks : List (List ℕ)) : List ℕ :=
  (List.replicate k 0).intercalate blocks

/-- Equal-width decimal blocks with `k` zeros between them are digits in
base `10 ^ (width + k)`. -/
private theorem spacedValue (w k : ℕ) (bs : List (List ℕ)) (h : ∀ b ∈ bs, b.length = w) :
    Nat.ofDigits 10 (spaced k bs) = Nat.ofDigits (10 ^ (w + k)) (bs.map (Nat.ofDigits 10)) := by
  induction bs with
  | nil => rfl
  | cons a tail ih =>
    cases tail with
    | nil => simp [spaced, Nat.ofDigits_cons]
    | cons b bs =>
      have ha := h a (by simp)
      have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
      simp only [spaced, List.intercalate_cons_cons, List.append_assoc, Nat.ofDigits_append,
        Nat.ofDigits_replicate_zero, List.length_replicate, zero_add, ha, List.map_cons,
        Nat.ofDigits_cons, pow_add] at ht ⊢
      rw [ht]
      simp only [mul_assoc]

private theorem spacedDigits (k : ℕ) (bs : List (List ℕ))
    (hs : ∀ b ∈ bs, ∀ d ∈ b, d < 10) : ∀ d ∈ spaced k bs, d < 10 := by
  induction bs with
  | nil => simp [spaced]
  | cons a tail ih =>
    cases tail with
    | nil => simpa [spaced] using hs a (by simp)
    | cons b bs =>
      have ha := hs a (by simp)
      have ht := ih (fun c hc => hs c (List.mem_cons_of_mem _ hc))
      intro d hd
      have hmem : d ∈ a ∨ d ∈ List.replicate k 0 ∨ d ∈ spaced k (b :: bs) := by
        simpa only [spaced, List.intercalate_cons_cons, List.append_assoc, List.mem_append] using hd
      rcases hmem with h | h | h
      · exact ha d h
      · obtain ⟨_, rfl⟩ := List.mem_replicate.mp h
        decide
      · exact ht d h

private theorem digitsOfWord {ds : List ℕ} (hs : ∀ d ∈ ds, d < 10)
    (hl : ds.getLast? = some 1) : Nat.digits 10 (Nat.ofDigits 10 ds) = ds := by
  apply Nat.digits_ofDigits 10 (by decide) _ hs
  intro h
  rw [List.getLast?_eq_some_getLast h] at hl
  simp_all

-- All blocks below are written least significant digit first.
private def rootBlocks : List (List ℕ) :=
  [[1,0,0], [1,1,0], [0,9,0], [0,1,1], [0,0,1]]

private def squareBlocks : List (List ℕ) :=
  [[1,0,0,0,0], [2,2,0,0,0], [1,0,3,0,0], [0,0,2,2,0], [0,2,7,0,1],
   [0,0,0,2,2], [0,0,1,0,3], [0,0,0,2,2], [0,0,0,0,1]]

private def reflectedBlocks : List (List ℕ) := (squareBlocks.map List.reverse).reverse

private def p (x : ℕ) : ℕ := 1 + 11*x + 90*x^2 + 110*x^3 + 100*x^4

private def q (x : ℕ) : ℕ := 1 + 11*x + (110*x - 9)*x^2 + 100*x^4

private theorem rootValue (k : ℕ) : Nat.ofDigits 10 (spaced (k+2) rootBlocks) = p (10^(5+k)) := by
  rw [spacedValue 3 _ _ (by decide), show 3 + (k + 2) = 5 + k by omega]
  change Nat.ofDigits _ [1,11,90,110,100] = _
  simp [Nat.ofDigits_cons, p]
  ring

private theorem squareValue (k : ℕ) : Nat.ofDigits 10 (spaced k squareBlocks) = p (10^(5+k)) ^ 2 := by
  rw [spacedValue 5 _ _ (by decide)]
  change Nat.ofDigits _ [1,22,301,2200,10720,22000,30100,22000,10000] = _
  simp [Nat.ofDigits_cons, p]
  ring

private theorem reflectedValue (k : ℕ) : Nat.ofDigits 10 (spaced k reflectedBlocks) = q (10^(5+k)) ^ 2 := by
  rw [spacedValue 5 _ _ (by decide)]
  change Nat.ofDigits _ [1,22,103,22,2701,220,10300,22000,10000] = _
  generalize hx : (10 : ℕ) ^ (5+k) = x
  have hxpos : 0 < x := hx ▸ (by positivity : 0 < (10 : ℕ) ^ (5+k))
  have h : 9 ≤ 110*x := by omega
  simp [Nat.ofDigits_cons, q]
  zify [h]
  ring

private theorem rootReversal (k : ℕ) : reverseDecimal (p (10^(5+k))) = p (10^(5+k)) := by
  let w := spaced (k+2) rootBlocks
  have hw : Nat.digits 10 (Nat.ofDigits 10 w) = w := by
    apply digitsOfWord (spacedDigits _ _ (by decide))
    simp only [spaced, rootBlocks, List.intercalate_cons_cons, List.intercalate_singleton,
      List.getLast?_append]
    rfl
  have hpal : w.reverse = w := by
    simp [w, spaced, rootBlocks, List.reverse_append, List.append_assoc]
  rw [← rootValue k]
  change Nat.ofDigits 10 (Nat.digits 10 (Nat.ofDigits 10 w)).reverse = Nat.ofDigits 10 w
  rw [hw, hpal]

private theorem squareReversal (k : ℕ) : reverseDecimal (p (10^(5+k)) ^ 2) = q (10^(5+k)) ^ 2 := by
  let w := spaced k squareBlocks
  have hw : Nat.digits 10 (Nat.ofDigits 10 w) = w := by
    apply digitsOfWord (spacedDigits _ _ (by decide))
    simp only [spaced, squareBlocks, List.intercalate_cons_cons, List.intercalate_singleton,
      List.getLast?_append]
    rfl
  have hrev : w.reverse = spaced k reflectedBlocks := by
    simp [w, spaced, squareBlocks, reflectedBlocks, List.reverse_append, List.append_assoc]
  rw [← squareValue k]
  change Nat.ofDigits 10 (Nat.digits 10 (Nat.ofDigits 10 w)).reverse = _
  rw [hw, hrev, reflectedValue]

private theorem q_lt_p {x : ℕ} (hx : 0 < x) : q x < p x := by
  have h : 9 ≤ 110*x := by omega
  have hid : q x + 99*x^2 = p x := by
    unfold q p
    zify [h]
    ring
  rw [← hid]
  have : 0 < 99*x^2 := by positivity
  omega

end OMA.S_oeis_a133901

open OMA.S_oeis_a133901 in
theorem OMA.solution : type_of% @OMA.S_oeis_a133901.main := by
  apply Set.infinite_of_forall_exists_gt
  intro k
  let x := (10 : ℕ)^(5+k)
  have hx : 0 < x := by dsimp [x]; positivity
  have hlarge : k < p x := by
    have hk : k < (10 : ℕ)^k := Nat.lt_pow_self (by decide)
    have hle : (10 : ℕ)^k ≤ x := by dsimp [x]; rw [pow_add]; omega
    unfold p
    omega
  refine ⟨p x, ⟨by omega, rootReversal k, ?_, q x, squareReversal k⟩, hlarge⟩
  rw [squareReversal k]
  exact (Nat.pow_lt_pow_left (q_lt_p hx) (by decide : 2 ≠ 0)).ne
