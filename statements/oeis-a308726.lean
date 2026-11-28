import Mathlib

/-!
# A308726: Mathar's recurrence

Source: https://oeis.org/A308726
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A308726 (offset 0): the number of permutations of length n and tier at most 1, that is, the number of permutations of length n sortable by two passes through a stack where outputting the longest prefix matching the identity permutation is prioritized;
data 1, 1, 2, 6, 24, 112, 556, 2811, 14234, 71808, 360568, 1803100, ...

Conjecture (R. J. Mathar, Jan 27 2020): D-finite with recurrence
3*n*(n-1)*(n+1)*a(n) -n*(n-1)*(67*n-101)*a(n-1)
+2*(n-1)*(286*n^2-1112*n+1089)*a(n-2) +4*(-580*n^3+4200*n^2-10106*n+8049)*a(n-3)
+24*(184*n^3-1784*n^2+5770*n-6221)*a(n-4) -96*(4*n-15)*(2*n-9)*(4*n-17)*a(n-5) = 0.

Formalization: The entry gives the g.f. (2 + (2*x-1)/sqrt(1-4*x) - sqrt(2*sqrt(1-4*x) - 1))/(2*x) (Vaclav Kotesovec,
Jun 30 2019), and this closed form is used as the definition here. T is the formal power series over ℚ
with T^2 = 1-4*x and constant term 1; W is the formal power series with W^2 = 2*T - 1 and constant term 1,
that is W = sqrt(2*sqrt(1-4x) - 1) (the constant terms select the branches of the square roots); and G
is determined by 2*x*T*G = 2*T + 2*x - 1 - W*T, the closed form multiplied by 2*x*T (its constant term
1 is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (360)*(112) + (-4680)*(24) + (21432)*(6) + (-39924)*(2) + (24696)*(1) + (-1440)*(1) = 0.
-/

namespace OMA.S_oeis_a308726

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A308726, for n ≥ 5. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 2 * T - 1 →
    coeff 0 W = 1 →
    2 * X * T * G = 2 * T + 2 * X - 1 - W * T →
    coeff 0 G = 1 →
    ∀ n : ℕ, 5 ≤ n →
      (-3 * (n : ℚ) + 3 * (n : ℚ) ^ 3) * coeff n G + (-101 * (n : ℚ) + 168 * (n : ℚ) ^ 2 - 67 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-2178 + 4402 * (n : ℚ) - 2796 * (n : ℚ) ^ 2 + 572 * (n : ℚ) ^ 3) * coeff (n - 2) G + (32196 - 40424 * (n : ℚ) + 16800 * (n : ℚ) ^ 2 - 2320 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-149304 + 138480 * (n : ℚ) - 42816 * (n : ℚ) ^ 2 + 4416 * (n : ℚ) ^ 3) * coeff (n - 4) G + (220320 - 159552 * (n : ℚ) + 38400 * (n : ℚ) ^ 2 - 3072 * (n : ℚ) ^ 3) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a308726
