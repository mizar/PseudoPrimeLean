/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticWide

/-! # Coverage through one hundred further analytic cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, one hundred certified analytic cells extend the `3/10`
witness bound for odd composites through logarithmic scale 193.98. Adjacent
closed endpoints connect each cell to the previous coverage. -/
theorem exists_reject_03_analytic19398 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (9699 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hprev : Real.log n ≤ (1051 / 10 : ℝ)
  · exact exists_reject_03_analytic1051 hn ho hc hGRH hL hprev
  by_cases h0 : Real.log n ≤ (5269 / 50 : ℝ)
  · exact gammaAnalyticWide0_witness hn ho hc hGRH hL (le_of_not_ge hprev) h0
  by_cases h1 : Real.log n ≤ (10567 / 100 : ℝ)
  · exact gammaAnalyticWide1_witness hn ho hc hGRH hL (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ (2649 / 25 : ℝ)
  · exact gammaAnalyticWide2_witness hn ho hc hGRH hL (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ (10627 / 100 : ℝ)
  · exact gammaAnalyticWide3_witness hn ho hc hGRH hL (le_of_not_ge h2) h3
  by_cases h4 : Real.log n ≤ (5329 / 50 : ℝ)
  · exact gammaAnalyticWide4_witness hn ho hc hGRH hL (le_of_not_ge h3) h4
  by_cases h5 : Real.log n ≤ (1069 / 10 : ℝ)
  · exact gammaAnalyticWide5_witness hn ho hc hGRH hL (le_of_not_ge h4) h5
  by_cases h6 : Real.log n ≤ (2681 / 25 : ℝ)
  · exact gammaAnalyticWide6_witness hn ho hc hGRH hL (le_of_not_ge h5) h6
  by_cases h7 : Real.log n ≤ (5379 / 50 : ℝ)
  · exact gammaAnalyticWide7_witness hn ho hc hGRH hL (le_of_not_ge h6) h7
  by_cases h8 : Real.log n ≤ (5397 / 50 : ℝ)
  · exact gammaAnalyticWide8_witness hn ho hc hGRH hL (le_of_not_ge h7) h8
  by_cases h9 : Real.log n ≤ (1083 / 10 : ℝ)
  · exact gammaAnalyticWide9_witness hn ho hc hGRH hL (le_of_not_ge h8) h9
  by_cases h10 : Real.log n ≤ (5433 / 50 : ℝ)
  · exact gammaAnalyticWide10_witness hn ho hc hGRH hL (le_of_not_ge h9) h10
  by_cases h11 : Real.log n ≤ (2726 / 25 : ℝ)
  · exact gammaAnalyticWide11_witness hn ho hc hGRH hL (le_of_not_ge h10) h11
  by_cases h12 : Real.log n ≤ (10941 / 100 : ℝ)
  · exact gammaAnalyticWide12_witness hn ho hc hGRH hL (le_of_not_ge h11) h12
  by_cases h13 : Real.log n ≤ (10981 / 100 : ℝ)
  · exact gammaAnalyticWide13_witness hn ho hc hGRH hL (le_of_not_ge h12) h13
  by_cases h14 : Real.log n ≤ (11021 / 100 : ℝ)
  · exact gammaAnalyticWide14_witness hn ho hc hGRH hL (le_of_not_ge h13) h14
  by_cases h15 : Real.log n ≤ (11061 / 100 : ℝ)
  · exact gammaAnalyticWide15_witness hn ho hc hGRH hL (le_of_not_ge h14) h15
  by_cases h16 : Real.log n ≤ (11103 / 100 : ℝ)
  · exact gammaAnalyticWide16_witness hn ho hc hGRH hL (le_of_not_ge h15) h16
  by_cases h17 : Real.log n ≤ (5573 / 50 : ℝ)
  · exact gammaAnalyticWide17_witness hn ho hc hGRH hL (le_of_not_ge h16) h17
  by_cases h18 : Real.log n ≤ (11189 / 100 : ℝ)
  · exact gammaAnalyticWide18_witness hn ho hc hGRH hL (le_of_not_ge h17) h18
  by_cases h19 : Real.log n ≤ (11233 / 100 : ℝ)
  · exact gammaAnalyticWide19_witness hn ho hc hGRH hL (le_of_not_ge h18) h19
  by_cases h20 : Real.log n ≤ (11279 / 100 : ℝ)
  · exact gammaAnalyticWide20_witness hn ho hc hGRH hL (le_of_not_ge h19) h20
  by_cases h21 : Real.log n ≤ (5663 / 50 : ℝ)
  · exact gammaAnalyticWide21_witness hn ho hc hGRH hL (le_of_not_ge h20) h21
  by_cases h22 : Real.log n ≤ (5687 / 50 : ℝ)
  · exact gammaAnalyticWide22_witness hn ho hc hGRH hL (le_of_not_ge h21) h22
  by_cases h23 : Real.log n ≤ (2856 / 25 : ℝ)
  · exact gammaAnalyticWide23_witness hn ho hc hGRH hL (le_of_not_ge h22) h23
  by_cases h24 : Real.log n ≤ (459 / 4 : ℝ)
  · exact gammaAnalyticWide24_witness hn ho hc hGRH hL (le_of_not_ge h23) h24
  by_cases h25 : Real.log n ≤ (5763 / 50 : ℝ)
  · exact gammaAnalyticWide25_witness hn ho hc hGRH hL (le_of_not_ge h24) h25
  by_cases h26 : Real.log n ≤ (5789 / 50 : ℝ)
  · exact gammaAnalyticWide26_witness hn ho hc hGRH hL (le_of_not_ge h25) h26
  by_cases h27 : Real.log n ≤ (11631 / 100 : ℝ)
  · exact gammaAnalyticWide27_witness hn ho hc hGRH hL (le_of_not_ge h26) h27
  by_cases h28 : Real.log n ≤ (5843 / 50 : ℝ)
  · exact gammaAnalyticWide28_witness hn ho hc hGRH hL (le_of_not_ge h27) h28
  by_cases h29 : Real.log n ≤ (11741 / 100 : ℝ)
  · exact gammaAnalyticWide29_witness hn ho hc hGRH hL (le_of_not_ge h28) h29
  by_cases h30 : Real.log n ≤ (5899 / 50 : ℝ)
  · exact gammaAnalyticWide30_witness hn ho hc hGRH hL (le_of_not_ge h29) h30
  by_cases h31 : Real.log n ≤ (2964 / 25 : ℝ)
  · exact gammaAnalyticWide31_witness hn ho hc hGRH hL (le_of_not_ge h30) h31
  by_cases h32 : Real.log n ≤ (2383 / 20 : ℝ)
  · exact gammaAnalyticWide32_witness hn ho hc hGRH hL (le_of_not_ge h31) h32
  by_cases h33 : Real.log n ≤ (11977 / 100 : ℝ)
  · exact gammaAnalyticWide33_witness hn ho hc hGRH hL (le_of_not_ge h32) h33
  by_cases h34 : Real.log n ≤ (12039 / 100 : ℝ)
  · exact gammaAnalyticWide34_witness hn ho hc hGRH hL (le_of_not_ge h33) h34
  by_cases h35 : Real.log n ≤ (12103 / 100 : ℝ)
  · exact gammaAnalyticWide35_witness hn ho hc hGRH hL (le_of_not_ge h34) h35
  by_cases h36 : Real.log n ≤ (3042 / 25 : ℝ)
  · exact gammaAnalyticWide36_witness hn ho hc hGRH hL (le_of_not_ge h35) h36
  by_cases h37 : Real.log n ≤ (12233 / 100 : ℝ)
  · exact gammaAnalyticWide37_witness hn ho hc hGRH hL (le_of_not_ge h36) h37
  by_cases h38 : Real.log n ≤ (12301 / 100 : ℝ)
  · exact gammaAnalyticWide38_witness hn ho hc hGRH hL (le_of_not_ge h37) h38
  by_cases h39 : Real.log n ≤ (1237 / 10 : ℝ)
  · exact gammaAnalyticWide39_witness hn ho hc hGRH hL (le_of_not_ge h38) h39
  by_cases h40 : Real.log n ≤ (622 / 5 : ℝ)
  · exact gammaAnalyticWide40_witness hn ho hc hGRH hL (le_of_not_ge h39) h40
  by_cases h41 : Real.log n ≤ (12511 / 100 : ℝ)
  · exact gammaAnalyticWide41_witness hn ho hc hGRH hL (le_of_not_ge h40) h41
  by_cases h42 : Real.log n ≤ (12583 / 100 : ℝ)
  · exact gammaAnalyticWide42_witness hn ho hc hGRH hL (le_of_not_ge h41) h42
  by_cases h43 : Real.log n ≤ (3164 / 25 : ℝ)
  · exact gammaAnalyticWide43_witness hn ho hc hGRH hL (le_of_not_ge h42) h43
  by_cases h44 : Real.log n ≤ (3183 / 25 : ℝ)
  · exact gammaAnalyticWide44_witness hn ho hc hGRH hL (le_of_not_ge h43) h44
  by_cases h45 : Real.log n ≤ (1281 / 10 : ℝ)
  · exact gammaAnalyticWide45_witness hn ho hc hGRH hL (le_of_not_ge h44) h45
  by_cases h46 : Real.log n ≤ (3222 / 25 : ℝ)
  · exact gammaAnalyticWide46_witness hn ho hc hGRH hL (le_of_not_ge h45) h46
  by_cases h47 : Real.log n ≤ (12969 / 100 : ℝ)
  · exact gammaAnalyticWide47_witness hn ho hc hGRH hL (le_of_not_ge h46) h47
  by_cases h48 : Real.log n ≤ (261 / 2 : ℝ)
  · exact gammaAnalyticWide48_witness hn ho hc hGRH hL (le_of_not_ge h47) h48
  by_cases h49 : Real.log n ≤ (6567 / 50 : ℝ)
  · exact gammaAnalyticWide49_witness hn ho hc hGRH hL (le_of_not_ge h48) h49
  by_cases h50 : Real.log n ≤ (13219 / 100 : ℝ)
  · exact gammaAnalyticWide50_witness hn ho hc hGRH hL (le_of_not_ge h49) h50
  by_cases h51 : Real.log n ≤ (2661 / 20 : ℝ)
  · exact gammaAnalyticWide51_witness hn ho hc hGRH hL (le_of_not_ge h50) h51
  by_cases h52 : Real.log n ≤ (3348 / 25 : ℝ)
  · exact gammaAnalyticWide52_witness hn ho hc hGRH hL (le_of_not_ge h51) h52
  by_cases h53 : Real.log n ≤ (13481 / 100 : ℝ)
  · exact gammaAnalyticWide53_witness hn ho hc hGRH hL (le_of_not_ge h52) h53
  by_cases h54 : Real.log n ≤ (3393 / 25 : ℝ)
  · exact gammaAnalyticWide54_witness hn ho hc hGRH hL (le_of_not_ge h53) h54
  by_cases h55 : Real.log n ≤ (13663 / 100 : ℝ)
  · exact gammaAnalyticWide55_witness hn ho hc hGRH hL (le_of_not_ge h54) h55
  by_cases h56 : Real.log n ≤ (13757 / 100 : ℝ)
  · exact gammaAnalyticWide56_witness hn ho hc hGRH hL (le_of_not_ge h55) h56
  by_cases h57 : Real.log n ≤ (3463 / 25 : ℝ)
  · exact gammaAnalyticWide57_witness hn ho hc hGRH hL (le_of_not_ge h56) h57
  by_cases h58 : Real.log n ≤ (13949 / 100 : ℝ)
  · exact gammaAnalyticWide58_witness hn ho hc hGRH hL (le_of_not_ge h57) h58
  by_cases h59 : Real.log n ≤ (3512 / 25 : ℝ)
  · exact gammaAnalyticWide59_witness hn ho hc hGRH hL (le_of_not_ge h58) h59
  by_cases h60 : Real.log n ≤ (3537 / 25 : ℝ)
  · exact gammaAnalyticWide60_witness hn ho hc hGRH hL (le_of_not_ge h59) h60
  by_cases h61 : Real.log n ≤ (14249 / 100 : ℝ)
  · exact gammaAnalyticWide61_witness hn ho hc hGRH hL (le_of_not_ge h60) h61
  by_cases h62 : Real.log n ≤ (14353 / 100 : ℝ)
  · exact gammaAnalyticWide62_witness hn ho hc hGRH hL (le_of_not_ge h61) h62
  by_cases h63 : Real.log n ≤ (7229 / 50 : ℝ)
  · exact gammaAnalyticWide63_witness hn ho hc hGRH hL (le_of_not_ge h62) h63
  by_cases h64 : Real.log n ≤ (2913 / 20 : ℝ)
  · exact gammaAnalyticWide64_witness hn ho hc hGRH hL (le_of_not_ge h63) h64
  by_cases h65 : Real.log n ≤ (7337 / 50 : ℝ)
  · exact gammaAnalyticWide65_witness hn ho hc hGRH hL (le_of_not_ge h64) h65
  by_cases h66 : Real.log n ≤ (14783 / 100 : ℝ)
  · exact gammaAnalyticWide66_witness hn ho hc hGRH hL (le_of_not_ge h65) h66
  by_cases h67 : Real.log n ≤ (2979 / 20 : ℝ)
  · exact gammaAnalyticWide67_witness hn ho hc hGRH hL (le_of_not_ge h66) h67
  by_cases h68 : Real.log n ≤ (3752 / 25 : ℝ)
  · exact gammaAnalyticWide68_witness hn ho hc hGRH hL (le_of_not_ge h67) h68
  by_cases h69 : Real.log n ≤ (15123 / 100 : ℝ)
  · exact gammaAnalyticWide69_witness hn ho hc hGRH hL (le_of_not_ge h68) h69
  by_cases h70 : Real.log n ≤ (762 / 5 : ℝ)
  · exact gammaAnalyticWide70_witness hn ho hc hGRH hL (le_of_not_ge h69) h70
  by_cases h71 : Real.log n ≤ (7679 / 50 : ℝ)
  · exact gammaAnalyticWide71_witness hn ho hc hGRH hL (le_of_not_ge h70) h71
  by_cases h72 : Real.log n ≤ (15479 / 100 : ℝ)
  · exact gammaAnalyticWide72_witness hn ho hc hGRH hL (le_of_not_ge h71) h72
  by_cases h73 : Real.log n ≤ (156 : ℝ)
  · exact gammaAnalyticWide73_witness hn ho hc hGRH hL (le_of_not_ge h72) h73
  by_cases h74 : Real.log n ≤ (15723 / 100 : ℝ)
  · exact gammaAnalyticWide74_witness hn ho hc hGRH hL (le_of_not_ge h73) h74
  by_cases h75 : Real.log n ≤ (15849 / 100 : ℝ)
  · exact gammaAnalyticWide75_witness hn ho hc hGRH hL (le_of_not_ge h74) h75
  by_cases h76 : Real.log n ≤ (3994 / 25 : ℝ)
  · exact gammaAnalyticWide76_witness hn ho hc hGRH hL (le_of_not_ge h75) h76
  by_cases h77 : Real.log n ≤ (4026 / 25 : ℝ)
  · exact gammaAnalyticWide77_witness hn ho hc hGRH hL (le_of_not_ge h76) h77
  by_cases h78 : Real.log n ≤ (3247 / 20 : ℝ)
  · exact gammaAnalyticWide78_witness hn ho hc hGRH hL (le_of_not_ge h77) h78
  by_cases h79 : Real.log n ≤ (4092 / 25 : ℝ)
  · exact gammaAnalyticWide79_witness hn ho hc hGRH hL (le_of_not_ge h78) h79
  by_cases h80 : Real.log n ≤ (8251 / 50 : ℝ)
  · exact gammaAnalyticWide80_witness hn ho hc hGRH hL (le_of_not_ge h79) h80
  by_cases h81 : Real.log n ≤ (8319 / 50 : ℝ)
  · exact gammaAnalyticWide81_witness hn ho hc hGRH hL (le_of_not_ge h80) h81
  by_cases h82 : Real.log n ≤ (4194 / 25 : ℝ)
  · exact gammaAnalyticWide82_witness hn ho hc hGRH hL (le_of_not_ge h81) h82
  by_cases h83 : Real.log n ≤ (4229 / 25 : ℝ)
  · exact gammaAnalyticWide83_witness hn ho hc hGRH hL (le_of_not_ge h82) h83
  by_cases h84 : Real.log n ≤ (8529 / 50 : ℝ)
  · exact gammaAnalyticWide84_witness hn ho hc hGRH hL (le_of_not_ge h83) h84
  by_cases h85 : Real.log n ≤ (8601 / 50 : ℝ)
  · exact gammaAnalyticWide85_witness hn ho hc hGRH hL (le_of_not_ge h84) h85
  by_cases h86 : Real.log n ≤ (17347 / 100 : ℝ)
  · exact gammaAnalyticWide86_witness hn ho hc hGRH hL (le_of_not_ge h85) h86
  by_cases h87 : Real.log n ≤ (8747 / 50 : ℝ)
  · exact gammaAnalyticWide87_witness hn ho hc hGRH hL (le_of_not_ge h86) h87
  by_cases h88 : Real.log n ≤ (17643 / 100 : ℝ)
  · exact gammaAnalyticWide88_witness hn ho hc hGRH hL (le_of_not_ge h87) h88
  by_cases h89 : Real.log n ≤ (17793 / 100 : ℝ)
  · exact gammaAnalyticWide89_witness hn ho hc hGRH hL (le_of_not_ge h88) h89
  by_cases h90 : Real.log n ≤ (3589 / 20 : ℝ)
  · exact gammaAnalyticWide90_witness hn ho hc hGRH hL (le_of_not_ge h89) h90
  by_cases h91 : Real.log n ≤ (18099 / 100 : ℝ)
  · exact gammaAnalyticWide91_witness hn ho hc hGRH hL (le_of_not_ge h90) h91
  by_cases h92 : Real.log n ≤ (3651 / 20 : ℝ)
  · exact gammaAnalyticWide92_witness hn ho hc hGRH hL (le_of_not_ge h91) h92
  by_cases h93 : Real.log n ≤ (18413 / 100 : ℝ)
  · exact gammaAnalyticWide93_witness hn ho hc hGRH hL (le_of_not_ge h92) h93
  by_cases h94 : Real.log n ≤ (18573 / 100 : ℝ)
  · exact gammaAnalyticWide94_witness hn ho hc hGRH hL (le_of_not_ge h93) h94
  by_cases h95 : Real.log n ≤ (9367 / 50 : ℝ)
  · exact gammaAnalyticWide95_witness hn ho hc hGRH hL (le_of_not_ge h94) h95
  by_cases h96 : Real.log n ≤ (18897 / 100 : ℝ)
  · exact gammaAnalyticWide96_witness hn ho hc hGRH hL (le_of_not_ge h95) h96
  by_cases h97 : Real.log n ≤ (9531 / 50 : ℝ)
  · exact gammaAnalyticWide97_witness hn ho hc hGRH hL (le_of_not_ge h96) h97
  by_cases h98 : Real.log n ≤ (19229 / 100 : ℝ)
  · exact gammaAnalyticWide98_witness hn ho hc hGRH hL (le_of_not_ge h97) h98
  exact gammaAnalyticWide99_witness hn ho hc hGRH hL (le_of_not_ge h98) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
