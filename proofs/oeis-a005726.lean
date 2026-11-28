import OMAStatements.S_oeis_a005726

/-! Proof. `a n` is the coefficient of `y^(2n+1)` in `P^n`, `P = 1+y+y²+y³ = (1+y)(1+y²)`.
The coefficients `T m k` of `P^m` satisfy the Pascal-type rule from `P^(m+1) = P·P^m` and the
first-order relation from `P·(P^m)' = m·P'·P^m`. The recurrence is a fixed polynomial combination
of these (Zeilberger-style certificate), after clearing a nonzero factor. -/

namespace OMA.S_oeis_a005726
open Polynomial Finset

noncomputable def P : ℤ[X] := 1 + X + X^2 + X^3
noncomputable def T (m k : ℕ) : ℤ := (P^m).coeff k

lemma pas (m k : ℕ) : T (m+1) (k+3) = T m (k+3) + T m (k+2) + T m (k+1) + T m k := by
  unfold T
  rw [pow_succ', P]
  simp only [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_X_pow_mul]

lemma Rr (m k : ℕ) : ((k:ℤ)+4) * T m (k+4) + ((k:ℤ)+3) * T m (k+3) + ((k:ℤ)+2) * T m (k+2)
    + ((k:ℤ)+1) * T m (k+1) = (m:ℤ) * (T m (k+3) + 2 * T m (k+2) + 3 * T m (k+1)) := by
  have hd : P * derivative (P^m) = (m:ℤ[X]) * (derivative P * P^m) := by
    rcases m with _ | m
    · simp
    · rw [derivative_pow, Nat.add_sub_cancel, ← C_eq_natCast]; ring
  have hP : derivative P = 1 + 2 * X + 3 * X^2 := by
    simp [P]
  have h := congrArg (fun q => q.coeff (k+3)) hd
  rw [hP, ← C_eq_natCast, coeff_C_mul] at h
  unfold T
  have e1 : ∀ q : ℤ[X], (P * q).coeff (k+3) = q.coeff (k+3) + q.coeff (k+2) + q.coeff (k+1) + q.coeff k := by
    intro q
    rw [P]; simp only [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_X_pow_mul]
  have e2 : ∀ q : ℤ[X], ((1 + 2*X + 3*X^2) * q).coeff (k+3) = q.coeff (k+3) + 2 * q.coeff (k+2) + 3 * q.coeff (k+1) := by
    intro q
    simp only [add_mul, one_mul, coeff_add, mul_assoc]
    rw [show (2:ℤ[X]) = C 2 by simp, show (3:ℤ[X]) = C 3 by simp, coeff_C_mul, coeff_C_mul, coeff_X_mul,
      show X^2 * q = q * X^2 by ring, show k + 3 = (k+1)+2 by ring, coeff_mul_X_pow]
  rw [e1, e2] at h
  simp only [coeff_derivative] at h
  push_cast at h
  linear_combination h

lemma aT (n : ℕ) : a n = T n (2*n+1) := by
  have hP : P^n = (1+X)^n * ∑ k ∈ range (n+1), (n.choose k : ℤ[X]) * X^(2*k) := by
    rw [show P = (1+X : ℤ[X])*(X^2+1) by unfold P; ring, mul_pow, add_pow (X^2 : ℤ[X]) 1 n]
    congr 1; exact Finset.sum_congr rfl (fun k _ => by rw [one_pow, mul_one, ← pow_mul]; ring)
  unfold T a
  rw [hP, mul_sum]
  simp only [finsetSum_coeff]
  have : ∀ k ∈ range (n+1), ((1+X)^n * ((n.choose k : ℤ[X]) * X^(2*k))).coeff (2*n+1)
      = ((n.choose (n-k) * n.choose (2*(n-k)+1) : ℕ) : ℤ) := by
    intro k hk
    have hk : k ≤ n := by simp at hk; omega
    rw [← C_eq_natCast, show (1+X)^n * (C (n.choose k : ℤ) * X^(2*k)) = C (n.choose k : ℤ) * ((1+X)^n * X^(2*k)) by ring,
      coeff_C_mul, coeff_mul_X_pow', if_pos (by omega), coeff_one_add_X_pow, Nat.choose_symm hk,
      show 2*n+1-2*k = 2*(n-k)+1 by omega]
    push_cast; ring
  have hr := sum_range_reflect (fun j => ((n.choose j * n.choose (2*j+1) : ℕ) : ℤ)) (n+1)
  simp only [Nat.add_sub_cancel] at hr
  rw [sum_congr rfl this, hr]
  apply sum_subset
  · intro x hx; simp at hx ⊢; omega
  · intro x _ hx
    simp at hx
    rw [Nat.choose_eq_zero_of_lt (n := n) (k := 2*x+1) (by omega)]; simp


theorem solution_main : ∀ n : ℕ, 4 ≤ n →
    let m : ℤ := n
    2 * (m - 1) * (2 * m + 1) * (13 * m - 14) * a n +
      (-143 * m ^ 3 + 297 * m ^ 2 - 148 * m + 12) * a (n - 1) -
      4 * (m - 1) * (26 * m ^ 2 - 41 * m + 9) * a (n - 2) -
      16 * (m - 1) * (m - 2) * (13 * m - 1) * a (n - 3) = 0 := by
  intro n hn
  intro m
  rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with h | h | h
  · subst h; simp only [m]; norm_num [a, Finset.sum_range_succ, Nat.choose]
  · subst h; simp only [m]; norm_num [a, Finset.sum_range_succ, Nat.choose]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 6 := ⟨n - 6, by omega⟩
  simp only [m, show N + 6 - 1 = N + 5 by omega, show N + 6 - 2 = N + 4 by omega,
    show N + 6 - 3 = N + 3 by omega, aT]
  have hD : (32*(N:ℤ)^4 + 560*(N:ℤ)^3 + 3640*(N:ℤ)^2 + 10420*(N:ℤ) + 11088 : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.mp (?_ : (32*(N:ℤ)^4 + 560*(N:ℤ)^3 + 3640*(N:ℤ)^2 + 10420*(N:ℤ) + 11088 : ℤ) * _ = 0)).resolve_left hD
  have h0 := Rr (N+3) (2*N+0)
  have h1 := Rr (N+3) (2*N+1)
  have h2 := Rr (N+3) (2*N+2)
  have h3 := Rr (N+3) (2*N+3)
  have h4 := Rr (N+4) (2*N+0)
  have h5 := Rr (N+4) (2*N+1)
  have h6 := Rr (N+4) (2*N+2)
  have h7 := Rr (N+4) (2*N+3)
  have h8 := Rr (N+4) (2*N+4)
  have h9 := Rr (N+4) (2*N+5)
  have h10 := Rr (N+5) (2*N+0)
  have h11 := Rr (N+5) (2*N+1)
  have h12 := Rr (N+5) (2*N+2)
  have h13 := Rr (N+5) (2*N+3)
  have h14 := Rr (N+5) (2*N+4)
  have h15 := Rr (N+5) (2*N+5)
  have h16 := Rr (N+5) (2*N+6)
  have h17 := Rr (N+5) (2*N+7)
  have h18 := Rr (N+6) (2*N+3)
  have h19 := Rr (N+6) (2*N+4)
  have h20 := Rr (N+6) (2*N+5)
  have h21 := Rr (N+6) (2*N+6)
  have h22 := Rr (N+6) (2*N+7)
  have h23 := Rr (N+6) (2*N+8)
  have h24 := Rr (N+6) (2*N+9)
  have h25 := pas (N+3) (2*N+1)
  have h26 := pas (N+3) (2*N+2)
  have h27 := pas (N+3) (2*N+3)
  have h28 := pas (N+4) (2*N+1)
  have h29 := pas (N+4) (2*N+2)
  have h30 := pas (N+4) (2*N+3)
  have h31 := pas (N+5) (2*N+1)
  have h32 := pas (N+5) (2*N+2)
  have h33 := pas (N+5) (2*N+3)
  push_cast at *
  ring_nf at *
  linear_combination (-1664*(N:ℤ)^6 - 48960*(N:ℤ)^5 - 598112*(N:ℤ)^4 - 3883248*(N:ℤ)^3 - 14132288*(N:ℤ)^2 - 27335088*(N:ℤ) - 21954240) * h0 + (-1664*(N:ℤ)^6 - 48960*(N:ℤ)^5 - 598112*(N:ℤ)^4 - 3883248*(N:ℤ)^3 - 14132288*(N:ℤ)^2 - 27335088*(N:ℤ) - 21954240) * h1 + (-1664*(N:ℤ)^5 - 41472*(N:ℤ)^4 - 411488*(N:ℤ)^3 - 2031552*(N:ℤ)^2 - 4990304*(N:ℤ) - 4878720) * h2 + (-3328*(N:ℤ)^6 - 96256*(N:ℤ)^5 - 1154752*(N:ℤ)^4 - 7355008*(N:ℤ)^3 - 26233024*(N:ℤ)^2 - 49679872*(N:ℤ) - 39029760) * h3 + (-1248*(N:ℤ)^6 - 38592*(N:ℤ)^5 - 494088*(N:ℤ)^4 - 3352464*(N:ℤ)^3 - 12715296*(N:ℤ)^2 - 25562448*(N:ℤ) - 21282624) * h4 + (-832*(N:ℤ)^6 - 26352*(N:ℤ)^5 - 344992*(N:ℤ)^4 - 2390436*(N:ℤ)^3 - 9248788*(N:ℤ)^2 - 18951336*(N:ℤ) - 16071264) * h5 + (-2704*(N:ℤ)^5 - 66864*(N:ℤ)^4 - 658108*(N:ℤ)^3 - 3222756*(N:ℤ)^2 - 7852072*(N:ℤ) - 7614816) * h6 + (-416*(N:ℤ)^6 - 12448*(N:ℤ)^5 - 154808*(N:ℤ)^4 - 1024120*(N:ℤ)^3 - 3800648*(N:ℤ)^2 - 7501480*(N:ℤ) - 6151200) * h7 + (832*(N:ℤ)^6 + 23648*(N:ℤ)^5 + 278512*(N:ℤ)^4 + 1739336*(N:ℤ)^3 + 6073456*(N:ℤ)^2 + 11240216*(N:ℤ) + 8611680) * h8 + (-1664*(N:ℤ)^6 - 47296*(N:ℤ)^5 - 557024*(N:ℤ)^4 - 3478672*(N:ℤ)^3 - 12146912*(N:ℤ)^2 - 22480432*(N:ℤ) - 17223360) * h9 + (-13*(N:ℤ)^6 - 649*(N:ℤ)^5 - 13345*(N:ℤ)^4 - 139855*(N:ℤ)^3 - 784762*(N:ℤ)^2 - 2246656*(N:ℤ) - 2580480) * h10 + (-299*(N:ℤ)^6 - 9922*(N:ℤ)^5 - 136799*(N:ℤ)^4 - 1005520*(N:ℤ)^3 - 4160876*(N:ℤ)^2 - 9193888*(N:ℤ) - 8472576) * h11 + (65*(N:ℤ)^6 + 840*(N:ℤ)^5 - 6475*(N:ℤ)^4 - 176742*(N:ℤ)^3 - 1237696*(N:ℤ)^2 - 3765648*(N:ℤ) - 4322304) * h12 + (1001*(N:ℤ)^6 + 30096*(N:ℤ)^5 + 372539*(N:ℤ)^4 + 2427672*(N:ℤ)^3 + 8771972*(N:ℤ)^2 + 16632816*(N:ℤ) + 12896064) * h13 + (-858*(N:ℤ)^6 - 26103*(N:ℤ)^5 - 329040*(N:ℤ)^4 - 2198805*(N:ℤ)^3 - 8211282*(N:ℤ)^2 - 16238232*(N:ℤ) - 13275360) * h14 + (-572*(N:ℤ)^6 - 16830*(N:ℤ)^5 - 204818*(N:ℤ)^4 - 1319220*(N:ℤ)^3 - 4741568*(N:ℤ)^2 - 9014400*(N:ℤ) - 7080192) * h15 + (1144*(N:ℤ)^6 + 31944*(N:ℤ)^5 + 369442*(N:ℤ)^4 + 2265150*(N:ℤ)^3 + 7765216*(N:ℤ)^2 + 14111616*(N:ℤ) + 10620288) * h16 + (-2288*(N:ℤ)^6 - 63888*(N:ℤ)^5 - 738884*(N:ℤ)^4 - 4530300*(N:ℤ)^3 - 15530432*(N:ℤ)^2 - 28223232*(N:ℤ) - 21240576) * h17 + (13*(N:ℤ)^6 + 649*(N:ℤ)^5 + 13345*(N:ℤ)^4 + 139855*(N:ℤ)^3 + 784762*(N:ℤ)^2 + 2246656*(N:ℤ) + 2580480) * h18 + (286*(N:ℤ)^6 + 9273*(N:ℤ)^5 + 123454*(N:ℤ)^4 + 865665*(N:ℤ)^3 + 3376114*(N:ℤ)^2 + 6947232*(N:ℤ) + 5892096) * h19 + (-364*(N:ℤ)^6 - 10762*(N:ℤ)^5 - 130324*(N:ℤ)^4 - 828778*(N:ℤ)^3 - 2923180*(N:ℤ)^2 - 5428240*(N:ℤ) - 4150272) * h20 + (312*(N:ℤ)^6 + 9336*(N:ℤ)^5 + 115074*(N:ℤ)^4 + 748050*(N:ℤ)^3 + 2705628*(N:ℤ)^2 + 5163984*(N:ℤ) + 4064256) * h21 + (208*(N:ℤ)^6 + 6016*(N:ℤ)^5 + 71740*(N:ℤ)^4 + 451840*(N:ℤ)^3 + 1586212*(N:ℤ)^2 + 2944144*(N:ℤ) + 2257920) * h22 + (-416*(N:ℤ)^6 - 11408*(N:ℤ)^5 - 129800*(N:ℤ)^4 - 784220*(N:ℤ)^3 - 2653124*(N:ℤ)^2 - 4764752*(N:ℤ) - 3548160) * h23 + (832*(N:ℤ)^6 + 22816*(N:ℤ)^5 + 259600*(N:ℤ)^4 + 1568440*(N:ℤ)^3 + 5306248*(N:ℤ)^2 + 9529504*(N:ℤ) + 7096320) * h24 + (1664*(N:ℤ)^7 + 62272*(N:ℤ)^6 + 989792*(N:ℤ)^5 + 8668144*(N:ℤ)^4 + 45198272*(N:ℤ)^3 + 140393392*(N:ℤ)^2 + 240634944*(N:ℤ) + 175633920) * h25 + (4992*(N:ℤ)^6 + 146880*(N:ℤ)^5 + 1794336*(N:ℤ)^4 + 11649744*(N:ℤ)^3 + 42396864*(N:ℤ)^2 + 82005264*(N:ℤ) + 65862720) * h26 + (-3328*(N:ℤ)^7 - 109568*(N:ℤ)^6 - 1536448*(N:ℤ)^5 - 11891072*(N:ℤ)^4 - 54830080*(N:ℤ)^3 - 150548864*(N:ℤ)^2 - 227768640*(N:ℤ) - 146361600) * h27 + (1248*(N:ℤ)^7 + 52320*(N:ℤ)^6 + 918600*(N:ℤ)^5 + 8787432*(N:ℤ)^4 + 49592400*(N:ℤ)^3 + 165430704*(N:ℤ)^2 + 302469552*(N:ℤ) + 234108864) * h28 + (-416*(N:ℤ)^7 - 10160*(N:ℤ)^6 - 78536*(N:ℤ)^5 + 17452*(N:ℤ)^4 + 3675532*(N:ℤ)^3 + 22300288*(N:ℤ)^2 + 56489760*(N:ℤ) + 54299520) * h29 + (-2080*(N:ℤ)^7 - 72640*(N:ℤ)^6 - 1072600*(N:ℤ)^5 - 8678416*(N:ℤ)^4 - 41532856*(N:ℤ)^3 - 117477328*(N:ℤ)^2 - 181639344*(N:ℤ) - 118236096) * h30 + (13*(N:ℤ)^7 + 831*(N:ℤ)^6 + 22431*(N:ℤ)^5 + 326685*(N:ℤ)^4 + 2742732*(N:ℤ)^3 + 13233324*(N:ℤ)^2 + 34033664*(N:ℤ) + 36126720) * h31 + (286*(N:ℤ)^7 + 13082*(N:ℤ)^6 + 248546*(N:ℤ)^5 + 2563982*(N:ℤ)^4 + 15608744*(N:ℤ)^3 + 56330048*(N:ℤ)^2 + 111932704*(N:ℤ) + 94660608) * h32 + (-377*(N:ℤ)^7 - 14063*(N:ℤ)^6 - 217175*(N:ℤ)^5 - 1791797*(N:ℤ)^4 - 8459288*(N:ℤ)^3 - 22496372*(N:ℤ)^2 - 30186240*(N:ℤ) - 14450688) * h33

end OMA.S_oeis_a005726

theorem OMA.solution : type_of% @OMA.S_oeis_a005726.main := OMA.S_oeis_a005726.solution_main
