import OMAStatements.S_oeis_a271356

/-!
# Proof of OEIS A271356 (Clark Kimberling's Fibonacci Product Gap Conjecture)

* Problem ID: `oeis-a271356` (`https://lefttosolve.com/p/oeis-a271356`)
* Original Conjecture: Clark Kimberling, OEIS A271356 (`https://oeis.org/A271356`),
  difference sequence of OEIS A271354 (`https://oeis.org/A271354`: products `F_i * F_j`
  of two distinct Fibonacci numbers greater than `1`, i.e., `3 ≤ i < j`).
* Claim: Every consecutive difference (gap) after the first gap (`6 → 10`, gap `4`)
  is a Fibonacci number.

## Mathematical Proof Summary (한국어 / English 요약)

1. **보조정리 (Cassini 및 Vajda 항등식)**:
   정수 피보나치 수열 `F n = (Nat.fib n : ℤ)`에 대하여 덧셈 정리 `Nat.fib_add`와 귀납법으로
   카시니 항등식 `F (n + 1) ^ 2 - F n * F (n + 2) = (-1) ^ n` 및 바이다(Vajda) 항등식
   `F (n + a) * F (n + b) - F n * F (n + a + b) = (-1) ^ n * F a * F b`를 증명한다.

2. **인덱스 합과 기우성에 따른 전순서 후속 사상 (`nextPair`)**:
   `(3, 4)` (곱 `6`) 이후의 모든 유효 인덱스 쌍 `ValidTail (i, j)` (`3 ≤ i < j` 이고 `8 ≤ i + j`)를
   인덱스 합 `s = i + j` 오름차순으로 묶고, 같은 합 `s` 내부에서는
   - 짝수 `i`를 오름차순 (`4, 6, 8, ...`)으로 배열한 뒤,
   - 중앙 전이(`j - i ∈ {1, 2, 3, 4}`)를 거쳐,
   - 홀수 `i`를 내림차순 (`..., 7, 5, 3`)으로 배열하고,
   - 블록의 최댓값 `(3, j)` (`2 * F_j`)에서 다음 합 `s + 1` 블록의 최솟값 `(4, j)` (`3 * F_j`)로
     넘어가는 명시적 후속 사상 `nextPair`를 정의한다.

3. **연속 차의 피보나치 수 판별 (`prodVal_nextPair`)**:
   모든 `ValidTail p`에 대하여 Vajda 항등식을 적용하면:
   - `i = 3 → (4, j)`: 차이는 `3 * F_j - 2 * F_j = F_j` (`> 0`).
   - 짝수 `i`, `i + 4 < j → (i + 2, j - 2)`: 차이는 `F (j - i - 2)` (`> 0`).
   - 짝수-홀수 중앙 전이 (`j - i ∈ {1, 2, 3, 4}`): 차이는 `F_2 = 1` 또는 `F_3 = 2` (`> 0`).
   - 홀수 `i ≥ 5 → (i - 2, j + 2)`: 차이는 `F (j - i + 2)` (`> 0`).
   따라서 `valSeq n = prodVal (pairSeq n)`은 엄격 단조증가(`StrictMono valSeq`)하며
   `n ≥ 1`에서 모든 인접 항의 차 `valSeq (n + 1) - valSeq n`은 양의 피보나치 수이다.

4. **전사성 (`isProduct_mem_valSeq`) 및 결론 (`OMA.solution`)**:
   역사상 `prevPair`가 `9 ≤ i + j`인 모든 유효 쌍의 정확한 역원(`nextPair (prevPair p) = p`)임을
   보여 강한 귀납법으로 모든 `IsProduct x`가 `valSeq`의 원소임을 증명한다. 엄격 단조증가성과
   전사성에 의해 첫 항(`valSeq 0 = 6`)보다 큰 임의의 인접한 두 곱 `x < y`는 `valSeq (k + 1)`과
   `valSeq (k + 2)`에 대응하므로, `y - x`는 항상 피보나치 수이다.
-/

namespace OMA.P_oeis_a271356

open OMA.S_oeis_a271356

def F (n : ℕ) : ℤ := (Nat.fib n : ℤ)

lemma F_zero : F 0 = 0 := by simp [F]
lemma F_one : F 1 = 1 := by simp [F]
lemma F_two : F 2 = 1 := by simp [F]
lemma F_three : F 3 = 2 := by decide
lemma F_four : F 4 = 3 := by decide

lemma F_add_two (n : ℕ) : F (n + 2) = F (n + 1) + F n := by
  simp only [F, Nat.fib_add_two, Nat.cast_add]
  ring

lemma F_add (m k : ℕ) : F (m + k + 1) = F m * F k + F (m + 1) * F (k + 1) := by
  simp only [F, Nat.fib_add, Nat.cast_add, Nat.cast_mul]

lemma cassini (n : ℕ) : F (n + 1) ^ 2 - F n * F (n + 2) = (-1 : ℤ) ^ n := by
  induction n with
  | zero =>
    rw [F_zero, F_one, F_two]
    norm_num
  | succ n ih =>
    change F (n + 2) ^ 2 - F (n + 1) * F (n + 3) = (-1 : ℤ) ^ (n + 1)
    have h2 : F (n + 3) = F (n + 2) + F (n + 1) := F_add_two (n + 1)
    have h1 : F (n + 2) = F (n + 1) + F n := F_add_two n
    rw [pow_succ, h2]
    linear_combination -ih + F (n + 2) * h1

lemma vajda (n a b : ℕ) :
    F (n + a) * F (n + b) - F n * F (n + a + b) = (-1 : ℤ) ^ n * F a * F b := by
  cases a with
  | zero =>
    simp [F_zero]
  | succ a =>
    cases b with
    | zero =>
      simp [F_zero]
      ring
    | succ b =>
      have ha : F (n + (a + 1)) = F n * F a + F (n + 1) * F (a + 1) := by
        simpa [Nat.add_assoc] using F_add n a
      have hb : F (n + (b + 1)) = F n * F b + F (n + 1) * F (b + 1) := by
        simpa [Nat.add_assoc] using F_add n b
      have hab1 : F (a + b + 1) = F a * F b + F (a + 1) * F (b + 1) := F_add a b
      have hab2 : F (a + b + 2) = F (a + 1) * F b + F (a + 2) * F (b + 1) := by
        have h := F_add (a + 1) b
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      have ha2 : F (a + 2) = F (a + 1) + F a := F_add_two a
      have hn2 : F (n + 2) = F (n + 1) + F n := F_add_two n
      have hnab : F (n + (a + 1) + (b + 1)) =
          F n * F (a + b + 1) + F (n + 1) * F (a + b + 2) := by
        have h := F_add n (a + b + 1)
        have heq : n + (a + 1) + (b + 1) = n + (a + b + 1) + 1 := by omega
        rw [heq]
        exact h
      rw [ha, hb, hnab, hab2, hab1, ha2]
      linear_combination (F (a + 1) * F (b + 1)) * cassini n +
        (F n * F (a + 1) * F (b + 1)) * hn2

def ValidPair (p : ℕ × ℕ) : Prop := 3 ≤ p.1 ∧ p.1 < p.2

def ValidTail (p : ℕ × ℕ) : Prop := ValidPair p ∧ 8 ≤ p.1 + p.2

def prodVal (p : ℕ × ℕ) : ℕ := Nat.fib p.1 * Nat.fib p.2

def nextPair (p : ℕ × ℕ) : ℕ × ℕ :=
  let i := p.1
  let j := p.2
  if i = 3 then (4, j)
  else if i % 2 = 0 then
    if i + 4 < j then (i + 2, j - 2)
    else if j = i + 1 then (i - 1, i + 2)
    else if j = i + 2 then (i - 1, i + 3)
    else if j = i + 3 then (i + 1, i + 2)
    else (i + 1, i + 3)
  else (i - 2, j + 2)

def gapIdx (p : ℕ × ℕ) : ℕ :=
  let i := p.1
  let j := p.2
  if i = 3 then j
  else if i % 2 = 0 then
    if i + 4 < j then j - i - 2
    else if j = i + 1 then 2
    else if j = i + 2 then 3
    else if j = i + 3 then 2
    else 3
  else j - i + 2

lemma nextPair_valid {p : ℕ × ℕ} (hp : ValidTail p) : ValidTail (nextPair p) := by
  rcases p with ⟨i, j⟩
  rcases hp with ⟨⟨hi3, hij⟩, hsum⟩
  dsimp [nextPair, ValidTail, ValidPair]
  split_ifs <;> omega

lemma gapIdx_pos {p : ℕ × ℕ} (hp : ValidTail p) : 0 < gapIdx p := by
  rcases p with ⟨i, j⟩
  rcases hp with ⟨⟨hi3, hij⟩, hsum⟩
  dsimp [gapIdx]
  split_ifs <;> omega

lemma neg_one_pow_even {k : ℕ} (h : k % 2 = 0) : (-1 : ℤ) ^ k = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
  simp [pow_mul]

lemma neg_one_pow_odd {k : ℕ} (h : k % 2 = 1) : (-1 : ℤ) ^ k = -1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  simp [pow_add, pow_mul]

lemma prodVal_nextPair {p : ℕ × ℕ} (hp : ValidTail p) :
    prodVal (nextPair p) = prodVal p + Nat.fib (gapIdx p) := by
  apply Nat.cast_injective (R := ℤ)
  rcases p with ⟨i, j⟩
  rcases hp with ⟨⟨hi3, hij⟩, hsum⟩
  simp only [Nat.cast_add, prodVal, Nat.cast_mul]
  change F (nextPair (i, j)).1 * F (nextPair (i, j)).2 =
    F i * F j + F (gapIdx (i, j))
  dsimp [nextPair, gapIdx]
  by_cases h3 : i = 3
  · rw [if_pos h3, if_pos h3]
    subst h3
    rw [F_four, F_three]
    ring
  · rw [if_neg h3, if_neg h3]
    by_cases hev : i % 2 = 0
    · rw [if_pos hev, if_pos hev]
      by_cases hfar : i + 4 < j
      · rw [if_pos hfar, if_pos hfar]
        have hv := vajda i 2 (j - i - 2)
        have h1 : i + (j - i - 2) = j - 2 := by omega
        have h2 : i + 2 + (j - i - 2) = j := by omega
        rw [h2, h1, neg_one_pow_even hev, F_two] at hv
        dsimp
        linarith
      · rw [if_neg hfar, if_neg hfar]
        by_cases hd1 : j = i + 1
        · rw [if_pos hd1, if_pos hd1]
          have hodd : (i - 1) % 2 = 1 := by omega
          have hv := vajda (i - 1) 1 2
          have h1 : i - 1 + 1 = i := by omega
          have h2 : i - 1 + 2 = i + 1 := by omega
          rw [h1, h2, neg_one_pow_odd hodd, F_one, F_two] at hv
          subst hd1
          rw [F_two]
          dsimp
          linarith
        · rw [if_neg hd1, if_neg hd1]
          by_cases hd2 : j = i + 2
          · rw [if_pos hd2, if_pos hd2]
            have hodd : (i - 1) % 2 = 1 := by omega
            have hv := vajda (i - 1) 1 3
            have h1 : i - 1 + 1 = i := by omega
            have h2 : i - 1 + 3 = i + 2 := by omega
            rw [h1, h2, neg_one_pow_odd hodd, F_one, F_three] at hv
            subst hd2
            rw [F_three]
            dsimp
            linarith
          · rw [if_neg hd2, if_neg hd2]
            by_cases hd3 : j = i + 3
            · rw [if_pos hd3, if_pos hd3]
              have hv := vajda i 1 2
              have h3' : i + 1 + 2 = i + 3 := by omega
              rw [h3', neg_one_pow_even hev, F_one, F_two] at hv
              subst hd3
              rw [F_two]
              dsimp
              linarith
            · rw [if_neg hd3, if_neg hd3]
              have hd4 : j = i + 4 := by omega
              have hv := vajda i 1 3
              have h4' : i + 1 + 3 = i + 4 := by omega
              rw [h4', neg_one_pow_even hev, F_one, F_three] at hv
              subst hd4
              rw [F_three]
              dsimp
              linarith
    · rw [if_neg hev, if_neg hev]
      have hodd : (i - 2) % 2 = 1 := by omega
      have hv := vajda (i - 2) 2 (j - i + 2)
      have h1 : i - 2 + 2 = i := by omega
      have h2 : i - 2 + (j - i + 2) = j := by omega
      have h3' : i + (j - i + 2) = j + 2 := by omega
      rw [h1, h2, h3', neg_one_pow_odd hodd, F_two] at hv
      dsimp
      linarith

def prevPair (p : ℕ × ℕ) : ℕ × ℕ :=
  let i := p.1
  let j := p.2
  if i = 4 then (3, j)
  else if i % 2 = 0 then (i - 2, j + 2)
  else if 5 ≤ j - i then (i + 2, j - 2)
  else if j - i ≤ 2 then (i - 1, j + 1)
  else (i + 1, j - 1)

lemma prevPair_valid {p : ℕ × ℕ} (hp : ValidPair p) (h9 : 9 ≤ p.1 + p.2) :
    ValidTail (prevPair p) := by
  rcases p with ⟨i, j⟩
  rcases hp with ⟨hi3, hij⟩
  dsimp [prevPair, ValidTail, ValidPair]
  split_ifs <;> omega

lemma nextPair_prevPair {p : ℕ × ℕ} (hp : ValidPair p) (h9 : 9 ≤ p.1 + p.2) :
    nextPair (prevPair p) = p := by
  rcases p with ⟨i, j⟩
  rcases hp with ⟨hi3, hij⟩
  dsimp [prevPair]
  by_cases h4 : i = 4
  · rw [if_pos h4]
    subst h4
    simp [nextPair]
  · rw [if_neg h4]
    by_cases hev : i % 2 = 0
    · rw [if_pos hev]
      dsimp [nextPair]
      have hne3 : i - 2 ≠ 3 := by omega
      have hev2 : (i - 2) % 2 = 0 := by omega
      have hfar : i - 2 + 4 < j + 2 := by omega
      rw [if_neg hne3, if_pos hev2, if_pos hfar]
      exact Prod.ext (by omega) (by omega)
    · rw [if_neg hev]
      by_cases h5 : 5 ≤ j - i
      · rw [if_pos h5]
        dsimp [nextPair]
        have hne3 : i + 2 ≠ 3 := by omega
        have hn_ev : ¬ (i + 2) % 2 = 0 := by omega
        rw [if_neg hne3, if_neg hn_ev]
        exact Prod.ext (by omega) (by omega)
      · rw [if_neg h5]
        by_cases hle2 : j - i ≤ 2
        · rw [if_pos hle2]
          dsimp [nextPair]
          have hne3 : i - 1 ≠ 3 := by omega
          have hev1 : (i - 1) % 2 = 0 := by omega
          have hnfar : ¬ (i - 1 + 4 < j + 1) := by omega
          have hne_d1 : j + 1 ≠ i - 1 + 1 := by omega
          have hne_d2 : j + 1 ≠ i - 1 + 2 := by omega
          rw [if_neg hne3, if_pos hev1, if_neg hnfar, if_neg hne_d1, if_neg hne_d2]
          by_cases hd3 : j + 1 = i - 1 + 3
          · rw [if_pos hd3]
            exact Prod.ext (by omega) (by omega)
          · rw [if_neg hd3]
            exact Prod.ext (by omega) (by omega)
        · rw [if_neg hle2]
          dsimp [nextPair]
          have hne3 : i + 1 ≠ 3 := by omega
          have hev1 : (i + 1) % 2 = 0 := by omega
          have hnfar : ¬ (i + 1 + 4 < j - 1) := by omega
          rw [if_neg hne3, if_pos hev1, if_neg hnfar]
          by_cases hd1 : j - 1 = i + 1 + 1
          · rw [if_pos hd1]
            exact Prod.ext (by omega) (by omega)
          · rw [if_neg hd1]
            have hd2 : j - 1 = i + 1 + 2 := by omega
            rw [if_pos hd2]
            exact Prod.ext (by omega) (by omega)

def pairSeq : ℕ → ℕ × ℕ
  | 0 => (3, 4)
  | 1 => (3, 5)
  | n + 2 => nextPair (pairSeq (n + 1))

def valSeq (n : ℕ) : ℕ := prodVal (pairSeq n)

lemma pairSeq_tail_valid (n : ℕ) : ValidTail (pairSeq (n + 1)) := by
  induction n with
  | zero =>
    dsimp [pairSeq, ValidTail, ValidPair]
    omega
  | succ n ih =>
    exact nextPair_valid ih

lemma pairSeq_valid (n : ℕ) : ValidPair (pairSeq n) := by
  cases n with
  | zero =>
    dsimp [pairSeq, ValidPair]
    omega
  | succ n =>
    exact (pairSeq_tail_valid n).1

lemma valSeq_succ_tail (n : ℕ) :
    valSeq (n + 2) = valSeq (n + 1) + Nat.fib (gapIdx (pairSeq (n + 1))) := by
  simpa [valSeq, pairSeq] using prodVal_nextPair (pairSeq_tail_valid n)

lemma valSeq_strictMono : StrictMono valSeq := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero =>
    decide
  | succ n =>
    rw [valSeq_succ_tail n]
    have hpos : 0 < Nat.fib (gapIdx (pairSeq (n + 1))) :=
      Nat.fib_pos.mpr (gapIdx_pos (pairSeq_tail_valid n))
    omega

lemma valSeq_isProduct (n : ℕ) : IsProduct (valSeq n) := by
  rcases hp : pairSeq n with ⟨i, j⟩
  have hv : ValidPair (i, j) := hp ▸ pairSeq_valid n
  exact ⟨i, j, hv.1, hv.2, by simp [valSeq, prodVal, hp]⟩

lemma surj_pairSeq_aux (M : ℕ) :
    ∀ p : ℕ × ℕ, prodVal p = M → ValidPair p → ∃ n : ℕ, pairSeq n = p := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro p hpM hp
    by_cases h9 : 9 ≤ p.1 + p.2
    · let q := prevPair p
      have hq : ValidTail q := prevPair_valid hp h9
      have hnq : nextPair q = p := nextPair_prevPair hp h9
      have hstep : prodVal p = prodVal q + Nat.fib (gapIdx q) := by
        rw [← hnq]
        exact prodVal_nextPair hq
      have hfpos : 0 < Nat.fib (gapIdx q) := Nat.fib_pos.mpr (gapIdx_pos hq)
      have hlt : prodVal q < M := by omega
      obtain ⟨m, hm⟩ := ih (prodVal q) hlt q rfl hq.1
      cases m with
      | zero =>
        exfalso
        have hsum0 : q.1 + q.2 = 7 := by
          rw [← hm]
          rfl
        have h8 := hq.2
        omega
      | succ k =>
        refine ⟨k + 2, ?_⟩
        simp [pairSeq, hm, hnq]
    · rcases p with ⟨i, j⟩
      rcases hp with ⟨hi3, hij⟩
      dsimp at h9
      have hcases : (i = 3 ∧ j = 4) ∨ (i = 3 ∧ j = 5) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩

lemma isProduct_mem_valSeq {x : ℕ} (hx : IsProduct x) : ∃ n : ℕ, valSeq n = x := by
  rcases hx with ⟨i, j, hi3, hij, rfl⟩
  obtain ⟨n, hn⟩ := surj_pairSeq_aux (prodVal (i, j)) (i, j) rfl ⟨hi3, hij⟩
  exact ⟨n, by simp [valSeq, prodVal, hn]⟩

end OMA.P_oeis_a271356

theorem OMA.solution : type_of% @OMA.S_oeis_a271356.main := by
  intro x y hx hy hxy hu hgap
  rcases OMA.P_oeis_a271356.isProduct_mem_valSeq hx with ⟨m, rfl⟩
  rcases OMA.P_oeis_a271356.isProduct_mem_valSeq hy with ⟨n, rfl⟩
  rcases hu with ⟨u, huP, hux⟩
  rcases OMA.P_oeis_a271356.isProduct_mem_valSeq huP with ⟨r, rfl⟩
  have hrm : r < m := OMA.P_oeis_a271356.valSeq_strictMono.lt_iff_lt.mp hux
  have hmn : m < n := OMA.P_oeis_a271356.valSeq_strictMono.lt_iff_lt.mp hxy
  have hne_zero : m ≠ 0 := by omega
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hn_eq : n = k + 2 := by
    by_contra hne
    have hlt1 : k + 1 < k + 2 := by omega
    have hlt2 : k + 2 < n := by omega
    exact hgap (OMA.P_oeis_a271356.valSeq (k + 2))
      (OMA.P_oeis_a271356.valSeq_strictMono hlt1)
      (OMA.P_oeis_a271356.valSeq_strictMono hlt2)
      (OMA.P_oeis_a271356.valSeq_isProduct (k + 2))
  subst hn_eq
  refine ⟨OMA.P_oeis_a271356.gapIdx (OMA.P_oeis_a271356.pairSeq (k + 1)), ?_⟩
  have hstep := OMA.P_oeis_a271356.valSeq_succ_tail k
  omega
