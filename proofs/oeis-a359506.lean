import OMAStatements.S_oeis_a359506

-- Problem: A359506: a(n) is the least integer m such that there exists a strictly increasing integer sequence n = b_1 < b_2 < ... < b_t = m with the property that b_1 XOR b_2 XOR ... XOR b_t = 0.
-- Upstream: formal-conjectures statements/oeis-a359506.lean:0 (declaration OMA.S_oeis_a359506.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(0) = 0, and for n >= 1 write n + 1 = 2^v * (2q + 1).
-- If q = 0 then v = w + 1 and a(n) = n + 2^w + 1 = 3(n+1)/2: the sequence n, 3*2^w - 1, 3*2^w
-- works, since n = 2^w + (2^w - 1), 3*2^w - 1 = 2^w*2 + (2^w - 1) and 3*2^w = 2^w*3.
-- If q >= 1 then a(n) = n + 2^(v+1) + 1: with m = n + 2^(v+1) + 1 the sequence n, n + 1, m - 1, m
-- works, since n XOR (n + 1) = (m - 1) XOR m = (2^v - 1) XOR 2^v.
-- Minimality: x -> x / 2^w is XOR-linear (Nat.xor_div_two_pow). For a smaller end m every
-- term after n has x / 2^w in {A, B} (A = 2q + 1, B = 2q + 2 with w = v; A = B = 2 with w the
-- exponent above), so the XOR of these terms has x / 2^w in {0, A, B, A XOR B}; but the XOR of
-- all terms is 0, so this XOR is n, and n / 2^w (= 2q, resp. 1) is not in that set.
-- Then a(n) >= n + 3 for n > 1 (2^w >= 2 there), a(4n) = 4n + 3 (v = 0, q = 2n), and
-- 3 a(n) <= 5(n + 1) since 3 * 2^v <= 2^v * (2q + 1).

namespace FS4A359506

theorem xd (w a b r s : ℕ) (hr : r < 2 ^ w) (hs : s < 2 ^ w) :
    (2 ^ w * a + r) ^^^ (2 ^ w * b + s) = 2 ^ w * (a ^^^ b) + (r ^^^ s) := by
  have hp : 0 < 2 ^ w := Nat.two_pow_pos w
  have h1 : (2 ^ w * a + r) / 2 ^ w = a := by
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hr, Nat.add_zero]
  have h2 : (2 ^ w * b + s) / 2 ^ w = b := by
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hs, Nat.add_zero]
  have h3 : (2 ^ w * a + r) % 2 ^ w = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have h4 : (2 ^ w * b + s) % 2 ^ w = s := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  have e := Nat.div_add_mod ((2 ^ w * a + r) ^^^ (2 ^ w * b + s)) (2 ^ w)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, h1, h2, h3, h4] at e
  exact e.symm

theorem fold_acc : ∀ (L : List ℕ) (c : ℕ),
    L.foldl (· ^^^ ·) c = c ^^^ L.foldl (· ^^^ ·) 0 := by
  intro L
  induction L with
  | nil => intro c; simp
  | cons b L ih =>
    intro c
    simp only [List.foldl_cons, Nat.zero_xor]
    rw [ih (c ^^^ b), ih b, Nat.xor_assoc]

theorem clos (A B y c : ℕ) (hy : y = 0 ∨ y = A ∨ y = B ∨ y = A ^^^ B) (hc : c = A ∨ c = B) :
    c ^^^ y = 0 ∨ c ^^^ y = A ∨ c ^^^ y = B ∨ c ^^^ y = A ^^^ B := by
  rcases hc with hc | hc <;> rcases hy with hy | hy | hy | hy <;> rw [hc, hy]
  · exact Or.inr (Or.inl (Nat.xor_zero A))
  · exact Or.inl (Nat.xor_self A)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl (by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor])))
  · exact Or.inr (Or.inr (Or.inl (Nat.xor_zero B)))
  · exact Or.inr (Or.inr (Or.inr (Nat.xor_comm B A)))
  · exact Or.inl (Nat.xor_self B)
  · exact Or.inr (Or.inl (by rw [Nat.xor_comm A B, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]))

theorem inv (w A B : ℕ) : ∀ L : List ℕ, (∀ b ∈ L, b / 2 ^ w = A ∨ b / 2 ^ w = B) →
    L.foldl (· ^^^ ·) 0 / 2 ^ w = 0 ∨ L.foldl (· ^^^ ·) 0 / 2 ^ w = A ∨
      L.foldl (· ^^^ ·) 0 / 2 ^ w = B ∨ L.foldl (· ^^^ ·) 0 / 2 ^ w = A ^^^ B := by
  intro L
  induction L with
  | nil => intro _; left; simp
  | cons b L ih =>
    intro h
    have hb := h b List.mem_cons_self
    have hL := ih (fun c hc => h c (List.mem_cons_of_mem b hc))
    simp only [List.foldl_cons, Nat.zero_xor]
    rw [fold_acc L b, Nat.xor_div_two_pow]
    exact clos A B _ _ hL hb

theorem le_last (l : List ℕ) (z : ℕ) (hp : l.Pairwise (· < ·)) (hl : l.getLast? = some z) :
    ∀ b ∈ l, b ≤ z := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  intro b hb
  rw [List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | hb
  · exact Nat.le_of_lt ((List.pairwise_append.mp hp).2.2 b hb z (List.mem_singleton.mpr rfl))
  · exact Nat.le_of_eq hb

theorem not_good (n m w A B : ℕ) (h0 : n / 2 ^ w ≠ 0) (hA : n / 2 ^ w ≠ A)
    (hB : n / 2 ^ w ≠ B) (hAB : n / 2 ^ w ≠ A ^^^ B)
    (hel : ∀ b, n < b → b ≤ m → b / 2 ^ w = A ∨ b / 2 ^ w = B) :
    ¬ OMA.S_oeis_a359506.Good n m := by
  rintro ⟨l, hp, hh, hl, hf⟩
  obtain ⟨L, rfl⟩ := List.head?_eq_some_iff.mp hh
  have hle := le_last _ _ hp hl
  have hlt := (List.pairwise_cons.mp hp).1
  have hL : ∀ b ∈ L, b / 2 ^ w = A ∨ b / 2 ^ w = B := fun b hb =>
    hel b (hlt b hb) (hle b (List.mem_cons_of_mem n hb))
  have hinv := inv w A B L hL
  simp only [List.foldl_cons, Nat.zero_xor] at hf
  rw [fold_acc] at hf
  have hX : L.foldl (· ^^^ ·) 0 = n := by
    calc L.foldl (· ^^^ ·) 0 = n ^^^ (n ^^^ L.foldl (· ^^^ ·) 0) := by
          rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      _ = n := by rw [hf, Nat.xor_zero]
  rw [hX] at hinv
  rcases hinv with h | h | h | h
  · exact h0 h
  · exact hA h
  · exact hB h
  · exact hAB h

theorem a_eq (n M : ℕ) (hg : OMA.S_oeis_a359506.Good n M)
    (hm : ∀ m < M, ¬ OMA.S_oeis_a359506.Good n m) : OMA.S_oeis_a359506.a n = M := by
  have h1 : sInf {m : ℕ | OMA.S_oeis_a359506.Good n m} ≤ M :=
    Nat.sInf_le (show M ∈ {m : ℕ | OMA.S_oeis_a359506.Good n m} from hg)
  have h2 : sInf {m : ℕ | OMA.S_oeis_a359506.Good n m} ∈
      {m : ℕ | OMA.S_oeis_a359506.Good n m} := Nat.sInf_mem ⟨M, hg⟩
  have h3 : ¬ sInf {m : ℕ | OMA.S_oeis_a359506.Good n m} < M := fun hlt => hm _ hlt h2
  show sInf {m : ℕ | OMA.S_oeis_a359506.Good n m} = M
  omega

theorem pw3 (a b c : ℕ) (h1 : a < b) (h2 : b < c) : [a, b, c].Pairwise (· < ·) := by
  simp
  omega

theorem pw4 (a b c d : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    [a, b, c, d].Pairwise (· < ·) := by
  simp
  omega

theorem a_zero : OMA.S_oeis_a359506.a 0 = 0 := by
  have hg : OMA.S_oeis_a359506.Good 0 0 := by
    refine ⟨[0], by simp, rfl, rfl, ?_⟩
    simp only [List.foldl_cons, List.foldl_nil, Nat.xor_self]
  have h := Nat.sInf_le (show 0 ∈ {m : ℕ | OMA.S_oeis_a359506.Good 0 m} from hg)
  show sInf {m : ℕ | OMA.S_oeis_a359506.Good 0 m} = 0
  omega

theorem val (n : ℕ) (hn : 0 < n) :
    (∃ w : ℕ, n + 1 = 2 * 2 ^ w ∧ OMA.S_oeis_a359506.a n = n + (2 ^ w + 1)) ∨
    (∃ v q : ℕ, 1 ≤ q ∧ n + 1 = 2 ^ v * (2 * q + 1) ∧
      OMA.S_oeis_a359506.a n = n + (2 ^ (v + 1) + 1)) := by
  obtain ⟨v, u, hu, hN⟩ := Nat.exists_eq_two_pow_mul_odd (show n + 1 ≠ 0 by omega)
  obtain ⟨q, rfl⟩ := hu
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    cases v with
    | zero =>
      rw [pow_zero] at hN
      omega
    | succ w =>
      left
      have hw : 0 < 2 ^ w := Nat.two_pow_pos w
      have hN' : n + 1 = 2 * 2 ^ w := by
        rw [hN]
        ring
      have hlt : 2 ^ w - 1 < 2 ^ w := by omega
      refine ⟨w, hN', a_eq n (n + (2 ^ w + 1)) ?_ ?_⟩
      · unfold OMA.S_oeis_a359506.Good
        refine ⟨[n, 2 ^ w * 2 + (2 ^ w - 1), n + (2 ^ w + 1)], ?_, rfl, rfl, ?_⟩
        · exact pw3 n (2 ^ w * 2 + (2 ^ w - 1)) (n + (2 ^ w + 1)) (by omega) (by omega)
        · have hA : n = 2 ^ w * 1 + (2 ^ w - 1) := by omega
          have hC : n + (2 ^ w + 1) = 2 ^ w * 3 := by omega
          show 0 ^^^ n ^^^ (2 ^ w * 2 + (2 ^ w - 1)) ^^^ (n + (2 ^ w + 1)) = 0
          rw [Nat.zero_xor, hC, hA, xd w 1 2 (2 ^ w - 1) (2 ^ w - 1) hlt hlt,
            Nat.xor_self (2 ^ w - 1), Nat.add_zero, show (1 ^^^ 2 : ℕ) = 3 by decide,
            Nat.xor_self]
      · intro k hk
        have hdiv : n / 2 ^ w = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        refine not_good n k w 2 2 (by rw [hdiv]; omega) (by rw [hdiv]; omega)
          (by rw [hdiv]; omega) (by rw [hdiv, Nat.xor_self]; omega) ?_
        intro b hb1 hb2
        have lo : 2 ≤ b / 2 ^ w := by
          rw [Nat.le_div_iff_mul_le hw]
          omega
        have hi : b / 2 ^ w < 3 := by
          rw [Nat.div_lt_iff_lt_mul hw]
          omega
        left
        omega
  · right
    have hP : 0 < 2 ^ v := Nat.two_pow_pos v
    have e1 : 2 ^ (v + 1) = 2 * 2 ^ v := by ring
    have r1 : 2 ^ v * (2 * q + 1) = 2 ^ (v + 1) * q + 2 ^ v := by ring
    have r2 : 2 ^ (v + 1) * (q + 1) = 2 ^ (v + 1) * q + 2 ^ (v + 1) := by ring
    have hl1 : 2 ^ v - 1 < 2 ^ (v + 1) := by omega
    have hl2 : 2 ^ v < 2 ^ (v + 1) := by omega
    refine ⟨v, q, by omega, hN, a_eq n (n + (2 ^ (v + 1) + 1)) ?_ ?_⟩
    · unfold OMA.S_oeis_a359506.Good
      refine ⟨[n, n + 1, 2 ^ (v + 1) * (q + 1) + (2 ^ v - 1), n + (2 ^ (v + 1) + 1)],
        ?_, rfl, rfl, ?_⟩
      · exact pw4 n (n + 1) (2 ^ (v + 1) * (q + 1) + (2 ^ v - 1))
          (n + (2 ^ (v + 1) + 1)) (by omega) (by omega) (by omega)
      · have hn : n = 2 ^ (v + 1) * q + (2 ^ v - 1) := by omega
        have hn1 : n + 1 = 2 ^ (v + 1) * q + 2 ^ v := by omega
        have hm : n + (2 ^ (v + 1) + 1) = 2 ^ (v + 1) * (q + 1) + 2 ^ v := by omega
        have hx1 : (2 ^ (v + 1) * q + (2 ^ v - 1)) ^^^ (2 ^ (v + 1) * q + 2 ^ v) =
            (2 ^ v - 1) ^^^ 2 ^ v := by
          rw [xd (v + 1) q q (2 ^ v - 1) (2 ^ v) hl1 hl2, Nat.xor_self q,
            Nat.mul_zero, Nat.zero_add]
        have hx2 : (2 ^ (v + 1) * (q + 1) + (2 ^ v - 1)) ^^^ (2 ^ (v + 1) * (q + 1) + 2 ^ v) =
            (2 ^ v - 1) ^^^ 2 ^ v := by
          rw [xd (v + 1) (q + 1) (q + 1) (2 ^ v - 1) (2 ^ v) hl1 hl2,
            Nat.xor_self (q + 1), Nat.mul_zero, Nat.zero_add]
        show 0 ^^^ n ^^^ (n + 1) ^^^ (2 ^ (v + 1) * (q + 1) + (2 ^ v - 1)) ^^^
          (n + (2 ^ (v + 1) + 1)) = 0
        rw [Nat.zero_xor, hm, hn1, hn, hx1, Nat.xor_assoc ((2 ^ v - 1) ^^^ 2 ^ v), hx2,
          Nat.xor_self]
    · intro k hk
      have hdiv : n / 2 ^ v = 2 * q := by
        have r3 : 2 * q * 2 ^ v + 2 ^ v = 2 ^ v * (2 * q + 1) := by ring
        have r4 : (2 * q + 1) * 2 ^ v = 2 ^ v * (2 * q + 1) := by ring
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have hpar : ((2 * q + 1) ^^^ (2 * q + 2)) % 2 = 1 := by
        have hm2 : ((2 * q + 1) ^^^ (2 * q + 2)) % 2 ^ 1 =
            (2 * q + 1) % 2 ^ 1 ^^^ (2 * q + 2) % 2 ^ 1 := Nat.xor_mod_two_pow
        rw [pow_one, show (2 * q + 1) % 2 = 1 by omega, show (2 * q + 2) % 2 = 0 by omega,
          Nat.xor_zero] at hm2
        exact hm2
      refine not_good n k v (2 * q + 1) (2 * q + 2) (by rw [hdiv]; omega)
        (by rw [hdiv]; omega) (by rw [hdiv]; omega) ?_ ?_
      · rw [hdiv]
        intro h
        rw [← h] at hpar
        omega
      · intro b hb1 hb2
        have r4 : (2 * q + 1) * 2 ^ v = 2 ^ v * (2 * q + 1) := by ring
        have r5 : (2 * q + 3) * 2 ^ v = 2 ^ v * (2 * q + 1) + 2 * 2 ^ v := by ring
        have lo : 2 * q + 1 ≤ b / 2 ^ v := by
          rw [Nat.le_div_iff_mul_le hP]
          omega
        have hi : b / 2 ^ v < 2 * q + 3 := by
          rw [Nat.div_lt_iff_lt_mul hP]
          omega
        omega

theorem part1 (n : ℕ) (hn : 1 < n) : n + 3 ≤ OMA.S_oeis_a359506.a n := by
  rcases val n (by omega) with ⟨w, hw, ha⟩ | ⟨v, q, hq, hv, ha⟩
  · rw [ha]
    omega
  · rw [ha]
    have e1 : 2 ^ (v + 1) = 2 * 2 ^ v := by ring
    have hP : 0 < 2 ^ v := Nat.two_pow_pos v
    omega

theorem part2 (n : ℕ) (hn : 0 < n) : OMA.S_oeis_a359506.a (4 * n) = 4 * n + 3 := by
  rcases val (4 * n) (by omega) with ⟨w, hw, ha⟩ | ⟨v, q, hq, hv, ha⟩
  · omega
  · cases v with
    | zero =>
      rw [ha]
      norm_num
    | succ v =>
      have e : 2 ^ (v + 1) * (2 * q + 1) = 2 * (2 ^ v * (2 * q + 1)) := by ring
      omega

theorem part3 (n : ℕ) : 3 * OMA.S_oeis_a359506.a n ≤ 5 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have h := a_zero
    omega
  · rcases val n hn with ⟨w, hw, ha⟩ | ⟨v, q, hq, hv, ha⟩
    · rw [ha]
      omega
    · rw [ha]
      have e1 : 2 ^ (v + 1) = 2 * 2 ^ v := by ring
      have h3 : 2 ^ v * 3 ≤ 2 ^ v * (2 * q + 1) :=
        Nat.mul_le_mul (le_refl (2 ^ v)) (show 3 ≤ 2 * q + 1 by omega)
      omega

end FS4A359506

theorem OMA.solution : type_of% @OMA.S_oeis_a359506.main := by
  refine ⟨FS4A359506.part1, FS4A359506.part2, fun n => ?_⟩
  have h := FS4A359506.part3 n
  have hq : (3 : ℚ) * (OMA.S_oeis_a359506.a n : ℚ) ≤ 5 * ((n : ℚ) + 1) := by
    exact_mod_cast h
  linarith
