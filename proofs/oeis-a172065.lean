import OMAStatements.S_oeis_a172065

-- Problem: A172065: Expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=8.
-- Upstream: formal-conjectures statements/oeis-a172065.lean:0 (declaration OMA.S_oeis_a172065.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A172065Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-256 * X ^ 8 + 1024 * X ^ 9 + (768 * X ^ 8) * S) = 256 - 2048 * X + 5120 * X ^ 2 - 4096 * X ^ 3 + 512 * X ^ 4 + (-256 + 1536 * X - 2560 * X ^ 2 + 1024 * X ^ 3) * S) :
    (137438953472 * X - 1443109011456 * X ^ 2 + 4879082848256 * X ^ 3 - 4604204941312 * X ^ 4 - 3298534883328 * X ^ 5 + 2954937499648 * X ^ 6 + 1374389534720 * X ^ 7) * derivative ℚ G + (1099511627776 - 10788957847552 * X + 33122787786752 * X ^ 2 - 25220047962112 * X ^ 3 - 24326694764544 * X ^ 4 + 14224931684352 * X ^ 5 + 7559142440960 * X ^ 6) * G = 1099511627776 + 343597383680 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d131072 : derivative ℚ (131072 : ℚ⟦X⟧) = 0 := dnum 131072
  have d262144 : derivative ℚ (262144 : ℚ⟦X⟧) = 0 := dnum 262144
  have d524288 : derivative ℚ (524288 : ℚ⟦X⟧) = 0 := dnum 524288
  have d655360 : derivative ℚ (655360 : ℚ⟦X⟧) = 0 := dnum 655360
  have d917504 : derivative ℚ (917504 : ℚ⟦X⟧) = 0 := dnum 917504
  have d1048576 : derivative ℚ (1048576 : ℚ⟦X⟧) = 0 := dnum 1048576
  have d1179648 : derivative ℚ (1179648 : ℚ⟦X⟧) = 0 := dnum 1179648
  have d1703936 : derivative ℚ (1703936 : ℚ⟦X⟧) = 0 := dnum 1703936
  have d1835008 : derivative ℚ (1835008 : ℚ⟦X⟧) = 0 := dnum 1835008
  have d2359296 : derivative ℚ (2359296 : ℚ⟦X⟧) = 0 := dnum 2359296
  have d3276800 : derivative ℚ (3276800 : ℚ⟦X⟧) = 0 := dnum 3276800
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-524288 * X ^ 16 + 1835008 * X ^ 17 + 1048576 * X ^ 18) * G = (131072 * X ^ 8 - 1179648 * X ^ 9 + 3276800 * X ^ 10 - 2359296 * X ^ 11 - 1179648 * X ^ 12 + 524288 * X ^ 13 : ℚ⟦X⟧) + (-131072 * X ^ 8 + 917504 * X ^ 9 - 1703936 * X ^ 10 + 262144 * X ^ 11 + 655360 * X ^ 12) * S := by
    linear_combination (-256 * X ^ 8 + 1024 * X ^ 9 - (768 * X ^ 8) * S) * hG + (768 * X ^ 8) * ((768 * X ^ 8) * G - (-256 + 1536 * X - 2560 * X ^ 2 + 1024 * X ^ 3)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-524288 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 1835008 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 1048576 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-8388608 * X ^ 15 + 31195136 * X ^ 16 + 18874368 * X ^ 17) * G + (-524288 * X ^ 16 + 1835008 * X ^ 17 + 1048576 * X ^ 18) * derivative ℚ G := by
    simp [Derivation.leibniz, d524288, d1048576, d1835008]
    ring
  have hR : derivative ℚ ((131072 * (X * X * X * X * X * X * X * X) - 1179648 * (X * X * X * X * X * X * X * X * X) + 3276800 * (X * X * X * X * X * X * X * X * X * X) - 2359296 * (X * X * X * X * X * X * X * X * X * X * X) - 1179648 * (X * X * X * X * X * X * X * X * X * X * X * X) + 524288 * (X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-131072 * (X * X * X * X * X * X * X * X) + 917504 * (X * X * X * X * X * X * X * X * X) - 1703936 * (X * X * X * X * X * X * X * X * X * X) + 262144 * (X * X * X * X * X * X * X * X * X * X * X) + 655360 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      1048576 * X ^ 7 - 10616832 * X ^ 8 + 32768000 * X ^ 9 - 25952256 * X ^ 10 - 14155776 * X ^ 11 + 6815744 * X ^ 12 + (-1048576 * X ^ 7 + 8257536 * X ^ 8 - 17039360 * X ^ 9 + 2883584 * X ^ 10 + 7864320 * X ^ 11) * S + (-131072 * X ^ 8 + 917504 * X ^ 9 - 1703936 * X ^ 10 + 262144 * X ^ 11 + 655360 * X ^ 12) * derivative ℚ S := by
    simp [Derivation.leibniz, d131072, d262144, d524288, d655360, d917504, d1179648, d1703936, d2359296, d3276800]
    ring
  have hk2 : (-524288 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 1835008 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 1048576 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (131072 * (X * X * X * X * X * X * X * X) - 1179648 * (X * X * X * X * X * X * X * X * X) + 3276800 * (X * X * X * X * X * X * X * X * X * X) - 2359296 * (X * X * X * X * X * X * X * X * X * X * X) - 1179648 * (X * X * X * X * X * X * X * X * X * X * X * X) + 524288 * (X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-131072 * (X * X * X * X * X * X * X * X) + 917504 * (X * X * X * X * X * X * X * X * X) - 1703936 * (X * X * X * X * X * X * X * X * X * X) + 262144 * (X * X * X * X * X * X * X * X * X * X * X) + 655360 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8388608 * X ^ 15 + 31195136 * X ^ 16 + 18874368 * X ^ 17) * G + (-524288 * X ^ 16 + 1835008 * X ^ 17 + 1048576 * X ^ 18) * derivative ℚ G =
      1048576 * X ^ 7 - 10616832 * X ^ 8 + 32768000 * X ^ 9 - 25952256 * X ^ 10 - 14155776 * X ^ 11 + 6815744 * X ^ 12 + (-1048576 * X ^ 7 + 8257536 * X ^ 8 - 17039360 * X ^ 9 + 2883584 * X ^ 10 + 7864320 * X ^ 11) * S + (-131072 * X ^ 8 + 917504 * X ^ 9 - 1703936 * X ^ 10 + 262144 * X ^ 11 + 655360 * X ^ 12) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 23 * ((1 - 4 * X) * ((137438953472 * X - 1443109011456 * X ^ 2 + 4879082848256 * X ^ 3 - 4604204941312 * X ^ 4 - 3298534883328 * X ^ 5 + 2954937499648 * X ^ 6 + 1374389534720 * X ^ 7) * derivative ℚ G + (1099511627776 - 10788957847552 * X + 33122787786752 * X ^ 2 - 25220047962112 * X ^ 3 - 24326694764544 * X ^ 4 + 14224931684352 * X ^ 5 + 7559142440960 * X ^ 6) * G - (1099511627776 + 343597383680 * X))) = 0 := by
    linear_combination (-131072 * X ^ 8 + 917504 * X ^ 9 - 1703936 * X ^ 10 + 262144 * X ^ 11 + 655360 * X ^ 12) ^ 2 * S * hdS - 2 * (-131072 * X ^ 8 + 917504 * X ^ 9 - 1703936 * X ^ 10 + 262144 * X ^ 11 + 655360 * X ^ 12) ^ 2 * derivative ℚ S * hS -
      (2 * (-1048576 * X ^ 7 + 8257536 * X ^ 8 - 17039360 * X ^ 9 + 2883584 * X ^ 10 + 7864320 * X ^ 11) * (1 - 4 * X) + (-131072 * X ^ 8 + 917504 * X ^ 9 - 1703936 * X ^ 10 + 262144 * X ^ 11 + 655360 * X ^ 12) * (-4)) * hk + 2 * (-131072 * X ^ 8 + 917504 * X ^ 9 - 1703936 * X ^ 10 + 262144 * X ^ 11 + 655360 * X ^ 12) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 23 ≠ 0 := pow_ne_zero 23 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-256 * X ^ 8 + 1024 * X ^ 9 + (768 * X ^ 8) * S) = 256 - 2048 * X + 5120 * X ^ 2 - 4096 * X ^ 3 + 512 * X ^ 4 + (-256 + 1536 * X - 2560 * X ^ 2 + 1024 * X ^ 3) * S) :
    (6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (92 * X ^ 2 - 373 * X ^ 3 - 250 * X ^ 4) * derivative ℚ (derivative ℚ G) + (288 * X - 1868 * X ^ 2 - 1480 * X ^ 3) * derivative ℚ G + (-2592 * X - 2420 * X ^ 2) * G =
      0 := by
  have h := key S G hS hG
  have d137438953472 : derivative ℚ (137438953472 : ℚ⟦X⟧) = 0 := dnum 137438953472
  have d343597383680 : derivative ℚ (343597383680 : ℚ⟦X⟧) = 0 := dnum 343597383680
  have d1099511627776 : derivative ℚ (1099511627776 : ℚ⟦X⟧) = 0 := dnum 1099511627776
  have d1374389534720 : derivative ℚ (1374389534720 : ℚ⟦X⟧) = 0 := dnum 1374389534720
  have d1443109011456 : derivative ℚ (1443109011456 : ℚ⟦X⟧) = 0 := dnum 1443109011456
  have d2886218022912 : derivative ℚ (2886218022912 : ℚ⟦X⟧) = 0 := dnum 2886218022912
  have d2954937499648 : derivative ℚ (2954937499648 : ℚ⟦X⟧) = 0 := dnum 2954937499648
  have d3298534883328 : derivative ℚ (3298534883328 : ℚ⟦X⟧) = 0 := dnum 3298534883328
  have d4604204941312 : derivative ℚ (4604204941312 : ℚ⟦X⟧) = 0 := dnum 4604204941312
  have d4879082848256 : derivative ℚ (4879082848256 : ℚ⟦X⟧) = 0 := dnum 4879082848256
  have d7559142440960 : derivative ℚ (7559142440960 : ℚ⟦X⟧) = 0 := dnum 7559142440960
  have d9620726743040 : derivative ℚ (9620726743040 : ℚ⟦X⟧) = 0 := dnum 9620726743040
  have d10788957847552 : derivative ℚ (10788957847552 : ℚ⟦X⟧) = 0 := dnum 10788957847552
  have d14224931684352 : derivative ℚ (14224931684352 : ℚ⟦X⟧) = 0 := dnum 14224931684352
  have d14637248544768 : derivative ℚ (14637248544768 : ℚ⟦X⟧) = 0 := dnum 14637248544768
  have d16492674416640 : derivative ℚ (16492674416640 : ℚ⟦X⟧) = 0 := dnum 16492674416640
  have d17729624997888 : derivative ℚ (17729624997888 : ℚ⟦X⟧) = 0 := dnum 17729624997888
  have d18416819765248 : derivative ℚ (18416819765248 : ℚ⟦X⟧) = 0 := dnum 18416819765248
  have d24326694764544 : derivative ℚ (24326694764544 : ℚ⟦X⟧) = 0 := dnum 24326694764544
  have d25220047962112 : derivative ℚ (25220047962112 : ℚ⟦X⟧) = 0 := dnum 25220047962112
  have d33122787786752 : derivative ℚ (33122787786752 : ℚ⟦X⟧) = 0 := dnum 33122787786752
  have d45354854645760 : derivative ℚ (45354854645760 : ℚ⟦X⟧) = 0 := dnum 45354854645760
  have d66245575573504 : derivative ℚ (66245575573504 : ℚ⟦X⟧) = 0 := dnum 66245575573504
  have d71124658421760 : derivative ℚ (71124658421760 : ℚ⟦X⟧) = 0 := dnum 71124658421760
  have d75660143886336 : derivative ℚ (75660143886336 : ℚ⟦X⟧) = 0 := dnum 75660143886336
  have d97306779058176 : derivative ℚ (97306779058176 : ℚ⟦X⟧) = 0 := dnum 97306779058176
  have hL : derivative ℚ ((137438953472 * X - 1443109011456 * (X * X) + 4879082848256 * (X * X * X) - 4604204941312 * (X * X * X * X) - 3298534883328 * (X * X * X * X * X) + 2954937499648 * (X * X * X * X * X * X) + 1374389534720 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (1099511627776 - 10788957847552 * X + 33122787786752 * (X * X) - 25220047962112 * (X * X * X) - 24326694764544 * (X * X * X * X) + 14224931684352 * (X * X * X * X * X) + 7559142440960 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (137438953472 - 2886218022912 * X + 14637248544768 * X ^ 2 - 18416819765248 * X ^ 3 - 16492674416640 * X ^ 4 + 17729624997888 * X ^ 5 + 9620726743040 * X ^ 6) * derivative ℚ G + (137438953472 * X - 1443109011456 * X ^ 2 + 4879082848256 * X ^ 3 - 4604204941312 * X ^ 4 - 3298534883328 * X ^ 5 + 2954937499648 * X ^ 6 + 1374389534720 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-10788957847552 + 66245575573504 * X - 75660143886336 * X ^ 2 - 97306779058176 * X ^ 3 + 71124658421760 * X ^ 4 + 45354854645760 * X ^ 5) * G + (1099511627776 - 10788957847552 * X + 33122787786752 * X ^ 2 - 25220047962112 * X ^ 3 - 24326694764544 * X ^ 4 + 14224931684352 * X ^ 5 + 7559142440960 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d137438953472, d1099511627776, d1374389534720, d1443109011456, d2954937499648, d3298534883328, d4604204941312, d4879082848256, d7559142440960, d10788957847552, d14224931684352, d24326694764544, d25220047962112, d33122787786752]
    ring
  have hRd : derivative ℚ (1099511627776 + 343597383680 * X : ℚ⟦X⟧) = 343597383680 := by
    simp [Derivation.leibniz, d343597383680, d1099511627776]
  have h2 : (137438953472 * X - 1443109011456 * (X * X) + 4879082848256 * (X * X * X) - 4604204941312 * (X * X * X * X) - 3298534883328 * (X * X * X * X * X) + 2954937499648 * (X * X * X * X * X * X) + 1374389534720 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (1099511627776 - 10788957847552 * X + 33122787786752 * (X * X) - 25220047962112 * (X * X * X) - 24326694764544 * (X * X * X * X) + 14224931684352 * (X * X * X * X * X) + 7559142440960 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (1099511627776 + 343597383680 * X : ℚ⟦X⟧) := by linear_combination h
  have hd : (137438953472 - 2886218022912 * X + 14637248544768 * X ^ 2 - 18416819765248 * X ^ 3 - 16492674416640 * X ^ 4 + 17729624997888 * X ^ 5 + 9620726743040 * X ^ 6) * derivative ℚ G + (137438953472 * X - 1443109011456 * X ^ 2 + 4879082848256 * X ^ 3 - 4604204941312 * X ^ 4 - 3298534883328 * X ^ 5 + 2954937499648 * X ^ 6 + 1374389534720 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-10788957847552 + 66245575573504 * X - 75660143886336 * X ^ 2 - 97306779058176 * X ^ 3 + 71124658421760 * X ^ 4 + 45354854645760 * X ^ 5) * G + (1099511627776 - 10788957847552 * X + 33122787786752 * X ^ 2 - 25220047962112 * X ^ 3 - 24326694764544 * X ^ 4 + 14224931684352 * X ^ 5 + 7559142440960 * X ^ 6) * derivative ℚ G = 343597383680 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((137438953472 - 2886218022912 * X + 14637248544768 * (X * X) - 18416819765248 * (X * X * X) - 16492674416640 * (X * X * X * X) + 17729624997888 * (X * X * X * X * X) + 9620726743040 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (137438953472 * X - 1443109011456 * (X * X) + 4879082848256 * (X * X * X) - 4604204941312 * (X * X * X * X) - 3298534883328 * (X * X * X * X * X) + 2954937499648 * (X * X * X * X * X * X) + 1374389534720 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-10788957847552 + 66245575573504 * X - 75660143886336 * (X * X) - 97306779058176 * (X * X * X) + 71124658421760 * (X * X * X * X) + 45354854645760 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (1099511627776 - 10788957847552 * X + 33122787786752 * (X * X) - 25220047962112 * (X * X * X) - 24326694764544 * (X * X * X * X) + 14224931684352 * (X * X * X * X * X) + 7559142440960 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-24464133718016 + 161765648236544 * X - 206570747068416 * X ^ 2 - 260584255782912 * X ^ 3 + 230897441832960 * X ^ 4 + 148434069749760 * X ^ 5) * derivative ℚ G + (1374389534720 - 16561393893376 * X + 62397284876288 * X ^ 2 - 62053687492608 * X ^ 3 - 57312043597824 * X ^ 4 + 49684181680128 * X ^ 5 + 26800595927040 * X ^ 6) * derivative ℚ (derivative ℚ G) + (137438953472 * X - 1443109011456 * X ^ 2 + 4879082848256 * X ^ 3 - 4604204941312 * X ^ 4 - 3298534883328 * X ^ 5 + 2954937499648 * X ^ 6 + 1374389534720 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (66245575573504 - 151320287772672 * X - 291920337174528 * X ^ 2 + 284498633687040 * X ^ 3 + 226774273228800 * X ^ 4) * G := by
    simp [Derivation.leibniz, d137438953472, d1099511627776, d1374389534720, d1443109011456, d2886218022912, d2954937499648, d3298534883328, d4604204941312, d4879082848256, d7559142440960, d9620726743040, d10788957847552, d14224931684352, d14637248544768, d16492674416640, d17729624997888, d18416819765248, d24326694764544, d25220047962112, d33122787786752, d45354854645760, d66245575573504, d71124658421760, d75660143886336, d97306779058176]
    ring
  have hRd2 : derivative ℚ (343597383680 : ℚ⟦X⟧) = 0 := by
    simp [d343597383680]
  have hdp : (137438953472 - 2886218022912 * X + 14637248544768 * (X * X) - 18416819765248 * (X * X * X) - 16492674416640 * (X * X * X * X) + 17729624997888 * (X * X * X * X * X) + 9620726743040 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (137438953472 * X - 1443109011456 * (X * X) + 4879082848256 * (X * X * X) - 4604204941312 * (X * X * X * X) - 3298534883328 * (X * X * X * X * X) + 2954937499648 * (X * X * X * X * X * X) + 1374389534720 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-10788957847552 + 66245575573504 * X - 75660143886336 * (X * X) - 97306779058176 * (X * X * X) + 71124658421760 * (X * X * X * X) + 45354854645760 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (1099511627776 - 10788957847552 * X + 33122787786752 * (X * X) - 25220047962112 * (X * X * X) - 24326694764544 * (X * X * X * X) + 14224931684352 * (X * X * X * X * X) + 7559142440960 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (343597383680 : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-24464133718016 + 161765648236544 * X - 206570747068416 * X ^ 2 - 260584255782912 * X ^ 3 + 230897441832960 * X ^ 4 + 148434069749760 * X ^ 5) * derivative ℚ G + (1374389534720 - 16561393893376 * X + 62397284876288 * X ^ 2 - 62053687492608 * X ^ 3 - 57312043597824 * X ^ 4 + 49684181680128 * X ^ 5 + 26800595927040 * X ^ 6) * derivative ℚ (derivative ℚ G) + (137438953472 * X - 1443109011456 * X ^ 2 + 4879082848256 * X ^ 3 - 4604204941312 * X ^ 4 - 3298534883328 * X ^ 5 + 2954937499648 * X ^ 6 + 1374389534720 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (66245575573504 - 151320287772672 * X - 291920337174528 * X ^ 2 + 284498633687040 * X ^ 3 + 226774273228800 * X ^ 4) * G = 0 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (68719476736 - 962072674304 * X + 5153960755200 * X ^ 2 - 12781822672896 * X ^ 3 + 12850542149632 * X ^ 4 + 1236950581248 * X ^ 5 - 8658654068736 * X ^ 6 + 1374389534720 * X ^ 7 + 1717986918400 * X ^ 8) * ((6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (92 * X ^ 2 - 373 * X ^ 3 - 250 * X ^ 4) * derivative ℚ (derivative ℚ G) + (288 * X - 1868 * X ^ 2 - 1480 * X ^ 3) * derivative ℚ G + (-2592 * X - 2420 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (3 * X ^ 2 - 21 * X ^ 3 + 39 * X ^ 4 - 6 * X ^ 5 - 15 * X ^ 6) * hd2 + (16 * X - 91 * X ^ 2 + 130 * X ^ 3 - 14 * X ^ 4 - 20 * X ^ 5) * hd + (-5 * X + 30 * X ^ 2 - 50 * X ^ 3 + 20 * X ^ 4) * h
  have hg : (68719476736 - 962072674304 * X + 5153960755200 * X ^ 2 - 12781822672896 * X ^ 3 + 12850542149632 * X ^ 4 + 1236950581248 * X ^ 5 - 8658654068736 * X ^ 6 + 1374389534720 * X ^ 7 + 1717986918400 * X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (68719476736 : ℚ⟦X⟧) = 68719476736 := cnum 68719476736
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-256 * X ^ 8 + 1024 * X ^ 9 + (768 * X ^ 8) * S) = 256 - 2048 * X + 5120 * X ^ 2 - 4096 * X ^ 3 + 512 * X ^ 4 + (-256 + 1536 * X - 2560 * X ^ 2 + 1024 * X ^ 3) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 6 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-21) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-12) + derivative ℚ (derivative ℚ G) * X * X * C 92 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-373) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-250) +
      derivative ℚ G * X * C 288 + derivative ℚ G * X * X * C (-1868) +
      derivative ℚ G * X * X * X * C (-1480) + G * X * C (-2592) +
      G * X * X * C (-2420) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-256 * X ^ 8 + 1024 * X ^ 9 + (768 * X ^ 8) * S) = 256 - 2048 * X + 5120 * X ^ 2 - 4096 * X ^ 3 + 512 * X ^ 4 + (-256 + 1536 * X - 2560 * X ^ 2 + 1024 * X ^ 3) * S) (m : ℕ) :
    6 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-21) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 92 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-373) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-250) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      288 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-1868) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1480) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-2592) * coeff (m + 1 + 1 + 1 + 1) G +
      (-2420) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-256 * X ^ 8 + 1024 * X ^ 9 + (768 * X ^ 8) * S) = 256 - 2048 * X + 5120 * X ^ 2 - 4096 * X ^ 3 + 512 * X ^ 4 + (-256 + 1536 * X - 2560 * X ^ 2 + 1024 * X ^ 3) * S) :
    184 * coeff (0 + 1 + 1) G + 576 * coeff (0 + 1 + 1) G +
      (-1868) * coeff (0 + 1) G + (-2592) * coeff (0 + 1) G +
      (-2420) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-256 * X ^ 8 + 1024 * X ^ 9 + (768 * X ^ 8) * S) = 256 - 2048 * X + 5120 * X ^ 2 - 4096 * X ^ 3 + 512 * X ^ 4 + (-256 + 1536 * X - 2560 * X ^ 2 + 1024 * X ^ 3) * S) :
    36 * coeff (0 + 1 + 1 + 1) G + 552 * coeff (0 + 1 + 1 + 1) G +
      (-746) * coeff (0 + 1 + 1) G + 864 * coeff (0 + 1 + 1 + 1) G +
      (-3736) * coeff (0 + 1 + 1) G + (-1480) * coeff (0 + 1) G +
      (-2592) * coeff (0 + 1 + 1) G + (-2420) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-256 * X ^ 8 + 1024 * X ^ 9 + (768 * X ^ 8) * S) = 256 - 2048 * X + 5120 * X ^ 2 - 4096 * X ^ 3 + 512 * X ^ 4 + (-256 + 1536 * X - 2560 * X ^ 2 + 1024 * X ^ 3) * S) :
    144 * coeff (0 + 1 + 1 + 1 + 1) G + (-126) * coeff (0 + 1 + 1 + 1) G +
      1104 * coeff (0 + 1 + 1 + 1 + 1) G + (-2238) * coeff (0 + 1 + 1 + 1) G +
      (-500) * coeff (0 + 1 + 1) G + 1152 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-5604) * coeff (0 + 1 + 1 + 1) G + (-2960) * coeff (0 + 1 + 1) G +
      (-2592) * coeff (0 + 1 + 1 + 1) G + (-2420) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A172065Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a172065.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A172065Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (256 * PowerSeries.X ^ 8) * hG - ((-2) + (14) * S + (-42) * S ^ 2 + (70) * S ^ 3 + (-70) * S ^ 4 + (42) * S ^ 5 + (-14) * S ^ 6 + (2) * S ^ 7 + (-4 * PowerSeries.X) * c + (24 * PowerSeries.X) * c * S + (-60 * PowerSeries.X) * c * S ^ 2 + (80 * PowerSeries.X) * c * S ^ 3 + (-60 * PowerSeries.X) * c * S ^ 4 + (24 * PowerSeries.X) * c * S ^ 5 + (-4 * PowerSeries.X) * c * S ^ 6 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (40 * PowerSeries.X ^ 2) * c ^ 2 * S + (-80 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (80 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-40 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (64 * PowerSeries.X ^ 3) * c ^ 3 * S + (-96 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (64 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (96 * PowerSeries.X ^ 4) * c ^ 4 * S + (-96 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (128 * PowerSeries.X ^ 5) * c ^ 5 * S + (-64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (128 * PowerSeries.X ^ 6) * c ^ 6 * S + (-256 * PowerSeries.X ^ 7) * c ^ 7) * hc - ((-254 + 1032 * PowerSeries.X - 992 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3) + (240 - 576 * PowerSeries.X + 256 * PowerSeries.X ^ 2) * S + (-198 + 240 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 2 + (128 - 64 * PowerSeries.X) * S ^ 3 + (-58 + 8 * PowerSeries.X) * S ^ 4 + (16) * S ^ 5 + (-2) * S ^ 6) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A172065Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (256 * PowerSeries.X ^ 8) * hG - ((-2) + (14) * S + (-42) * S ^ 2 + (70) * S ^ 3 + (-70) * S ^ 4 + (42) * S ^ 5 + (-14) * S ^ 6 + (2) * S ^ 7 + (-4 * PowerSeries.X) * c + (24 * PowerSeries.X) * c * S + (-60 * PowerSeries.X) * c * S ^ 2 + (80 * PowerSeries.X) * c * S ^ 3 + (-60 * PowerSeries.X) * c * S ^ 4 + (24 * PowerSeries.X) * c * S ^ 5 + (-4 * PowerSeries.X) * c * S ^ 6 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (40 * PowerSeries.X ^ 2) * c ^ 2 * S + (-80 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (80 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-40 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (64 * PowerSeries.X ^ 3) * c ^ 3 * S + (-96 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (64 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (96 * PowerSeries.X ^ 4) * c ^ 4 * S + (-96 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (128 * PowerSeries.X ^ 5) * c ^ 5 * S + (-64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (128 * PowerSeries.X ^ 6) * c ^ 6 * S + (-256 * PowerSeries.X ^ 7) * c ^ 7) * hc - ((-254 + 1032 * PowerSeries.X - 992 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3) + (240 - 576 * PowerSeries.X + 256 * PowerSeries.X ^ 2) * S + (-198 + 240 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 2 + (128 - 64 * PowerSeries.X) * S ^ 3 + (-58 + 8 * PowerSeries.X) * S ^ 4 + (16) * S ^ 5 + (-2) * S ^ 6) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A172065Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination (256 * PowerSeries.X ^ 8) * hG - ((-2) + (14) * S + (-42) * S ^ 2 + (70) * S ^ 3 + (-70) * S ^ 4 + (42) * S ^ 5 + (-14) * S ^ 6 + (2) * S ^ 7 + (-4 * PowerSeries.X) * c + (24 * PowerSeries.X) * c * S + (-60 * PowerSeries.X) * c * S ^ 2 + (80 * PowerSeries.X) * c * S ^ 3 + (-60 * PowerSeries.X) * c * S ^ 4 + (24 * PowerSeries.X) * c * S ^ 5 + (-4 * PowerSeries.X) * c * S ^ 6 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (40 * PowerSeries.X ^ 2) * c ^ 2 * S + (-80 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (80 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-40 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (64 * PowerSeries.X ^ 3) * c ^ 3 * S + (-96 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (64 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (96 * PowerSeries.X ^ 4) * c ^ 4 * S + (-96 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (128 * PowerSeries.X ^ 5) * c ^ 5 * S + (-64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (128 * PowerSeries.X ^ 6) * c ^ 6 * S + (-256 * PowerSeries.X ^ 7) * c ^ 7) * hc - ((-254 + 1032 * PowerSeries.X - 992 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3) + (240 - 576 * PowerSeries.X + 256 * PowerSeries.X ^ 2) * S + (-198 + 240 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 2 + (128 - 64 * PowerSeries.X) * S ^ 3 + (-58 + 8 * PowerSeries.X) * S ^ 4 + (16) * S ^ 5 + (-2) * S ^ 6) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A172065Aux.rel (S) G (by linear_combination hS)
            (by linear_combination (256 * PowerSeries.X ^ 8) * hG - ((-2) + (14) * S + (-42) * S ^ 2 + (70) * S ^ 3 + (-70) * S ^ 4 + (42) * S ^ 5 + (-14) * S ^ 6 + (2) * S ^ 7 + (-4 * PowerSeries.X) * c + (24 * PowerSeries.X) * c * S + (-60 * PowerSeries.X) * c * S ^ 2 + (80 * PowerSeries.X) * c * S ^ 3 + (-60 * PowerSeries.X) * c * S ^ 4 + (24 * PowerSeries.X) * c * S ^ 5 + (-4 * PowerSeries.X) * c * S ^ 6 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (40 * PowerSeries.X ^ 2) * c ^ 2 * S + (-80 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (80 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-40 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (64 * PowerSeries.X ^ 3) * c ^ 3 * S + (-96 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (64 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (96 * PowerSeries.X ^ 4) * c ^ 4 * S + (-96 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (128 * PowerSeries.X ^ 5) * c ^ 5 * S + (-64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (128 * PowerSeries.X ^ 6) * c ^ 6 * S + (-256 * PowerSeries.X ^ 7) * c ^ 7) * hc - ((-254 + 1032 * PowerSeries.X - 992 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3) + (240 - 576 * PowerSeries.X + 256 * PowerSeries.X ^ 2) * S + (-198 + 240 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 2 + (128 - 64 * PowerSeries.X) * S ^ 3 + (-58 + 8 * PowerSeries.X) * S ^ 4 + (16) * S ^ 5 + (-2) * S ^ 6) * hS) m
        push_cast
        linear_combination r
