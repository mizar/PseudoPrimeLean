/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticBridge

/-! # Coverage through 91 further analytic cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, 91 certified analytic cells extend the `3/10`
witness bound for odd composites through logarithmic scale 1000. Adjacent
closed endpoints connect each cell to the previous coverage. -/
theorem exists_reject_03_analytic1000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (1000 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hprev : Real.log n ≤ (550 : ℝ)
  · exact exists_reject_03_analytic550 hn ho hc hGRH hL hprev
  by_cases h0 : Real.log n ≤ (11093 / 20 : ℝ)
  · exact gammaAnalyticBridge0_witness hn ho hc hGRH hL (le_of_not_ge hprev) h0
  by_cases h1 : Real.log n ≤ (55933 / 100 : ℝ)
  · exact gammaAnalyticBridge1_witness hn ho hc hGRH hL (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ (11281 / 20 : ℝ)
  · exact gammaAnalyticBridge2_witness hn ho hc hGRH hL (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ (56881 / 100 : ℝ)
  · exact gammaAnalyticBridge3_witness hn ho hc hGRH hL (le_of_not_ge h2) h3
  by_cases h4 : Real.log n ≤ (2868 / 5 : ℝ)
  · exact gammaAnalyticBridge4_witness hn ho hc hGRH hL (le_of_not_ge h3) h4
  by_cases h5 : Real.log n ≤ (57843 / 100 : ℝ)
  · exact gammaAnalyticBridge5_witness hn ho hc hGRH hL (le_of_not_ge h4) h5
  by_cases h6 : Real.log n ≤ (58329 / 100 : ℝ)
  · exact gammaAnalyticBridge6_witness hn ho hc hGRH hL (le_of_not_ge h5) h6
  by_cases h7 : Real.log n ≤ (2941 / 5 : ℝ)
  · exact gammaAnalyticBridge7_witness hn ho hc hGRH hL (le_of_not_ge h6) h7
  by_cases h8 : Real.log n ≤ (29657 / 50 : ℝ)
  · exact gammaAnalyticBridge8_witness hn ho hc hGRH hL (le_of_not_ge h7) h8
  by_cases h9 : Real.log n ≤ (14953 / 25 : ℝ)
  · exact gammaAnalyticBridge9_witness hn ho hc hGRH hL (le_of_not_ge h8) h9
  by_cases h10 : Real.log n ≤ (15078 / 25 : ℝ)
  · exact gammaAnalyticBridge10_witness hn ho hc hGRH hL (le_of_not_ge h9) h10
  by_cases h11 : Real.log n ≤ (15203 / 25 : ℝ)
  · exact gammaAnalyticBridge11_witness hn ho hc hGRH hL (le_of_not_ge h10) h11
  by_cases h12 : Real.log n ≤ (15328 / 25 : ℝ)
  · exact gammaAnalyticBridge12_witness hn ho hc hGRH hL (le_of_not_ge h11) h12
  by_cases h13 : Real.log n ≤ (15453 / 25 : ℝ)
  · exact gammaAnalyticBridge13_witness hn ho hc hGRH hL (le_of_not_ge h12) h13
  by_cases h14 : Real.log n ≤ (15578 / 25 : ℝ)
  · exact gammaAnalyticBridge14_witness hn ho hc hGRH hL (le_of_not_ge h13) h14
  by_cases h15 : Real.log n ≤ (15703 / 25 : ℝ)
  · exact gammaAnalyticBridge15_witness hn ho hc hGRH hL (le_of_not_ge h14) h15
  by_cases h16 : Real.log n ≤ (15828 / 25 : ℝ)
  · exact gammaAnalyticBridge16_witness hn ho hc hGRH hL (le_of_not_ge h15) h16
  by_cases h17 : Real.log n ≤ (15953 / 25 : ℝ)
  · exact gammaAnalyticBridge17_witness hn ho hc hGRH hL (le_of_not_ge h16) h17
  by_cases h18 : Real.log n ≤ (16078 / 25 : ℝ)
  · exact gammaAnalyticBridge18_witness hn ho hc hGRH hL (le_of_not_ge h17) h18
  by_cases h19 : Real.log n ≤ (16203 / 25 : ℝ)
  · exact gammaAnalyticBridge19_witness hn ho hc hGRH hL (le_of_not_ge h18) h19
  by_cases h20 : Real.log n ≤ (16328 / 25 : ℝ)
  · exact gammaAnalyticBridge20_witness hn ho hc hGRH hL (le_of_not_ge h19) h20
  by_cases h21 : Real.log n ≤ (16453 / 25 : ℝ)
  · exact gammaAnalyticBridge21_witness hn ho hc hGRH hL (le_of_not_ge h20) h21
  by_cases h22 : Real.log n ≤ (16578 / 25 : ℝ)
  · exact gammaAnalyticBridge22_witness hn ho hc hGRH hL (le_of_not_ge h21) h22
  by_cases h23 : Real.log n ≤ (16703 / 25 : ℝ)
  · exact gammaAnalyticBridge23_witness hn ho hc hGRH hL (le_of_not_ge h22) h23
  by_cases h24 : Real.log n ≤ (16828 / 25 : ℝ)
  · exact gammaAnalyticBridge24_witness hn ho hc hGRH hL (le_of_not_ge h23) h24
  by_cases h25 : Real.log n ≤ (16953 / 25 : ℝ)
  · exact gammaAnalyticBridge25_witness hn ho hc hGRH hL (le_of_not_ge h24) h25
  by_cases h26 : Real.log n ≤ (17078 / 25 : ℝ)
  · exact gammaAnalyticBridge26_witness hn ho hc hGRH hL (le_of_not_ge h25) h26
  by_cases h27 : Real.log n ≤ (17203 / 25 : ℝ)
  · exact gammaAnalyticBridge27_witness hn ho hc hGRH hL (le_of_not_ge h26) h27
  by_cases h28 : Real.log n ≤ (17328 / 25 : ℝ)
  · exact gammaAnalyticBridge28_witness hn ho hc hGRH hL (le_of_not_ge h27) h28
  by_cases h29 : Real.log n ≤ (17453 / 25 : ℝ)
  · exact gammaAnalyticBridge29_witness hn ho hc hGRH hL (le_of_not_ge h28) h29
  by_cases h30 : Real.log n ≤ (17578 / 25 : ℝ)
  · exact gammaAnalyticBridge30_witness hn ho hc hGRH hL (le_of_not_ge h29) h30
  by_cases h31 : Real.log n ≤ (17703 / 25 : ℝ)
  · exact gammaAnalyticBridge31_witness hn ho hc hGRH hL (le_of_not_ge h30) h31
  by_cases h32 : Real.log n ≤ (17828 / 25 : ℝ)
  · exact gammaAnalyticBridge32_witness hn ho hc hGRH hL (le_of_not_ge h31) h32
  by_cases h33 : Real.log n ≤ (17953 / 25 : ℝ)
  · exact gammaAnalyticBridge33_witness hn ho hc hGRH hL (le_of_not_ge h32) h33
  by_cases h34 : Real.log n ≤ (18078 / 25 : ℝ)
  · exact gammaAnalyticBridge34_witness hn ho hc hGRH hL (le_of_not_ge h33) h34
  by_cases h35 : Real.log n ≤ (18203 / 25 : ℝ)
  · exact gammaAnalyticBridge35_witness hn ho hc hGRH hL (le_of_not_ge h34) h35
  by_cases h36 : Real.log n ≤ (18328 / 25 : ℝ)
  · exact gammaAnalyticBridge36_witness hn ho hc hGRH hL (le_of_not_ge h35) h36
  by_cases h37 : Real.log n ≤ (18453 / 25 : ℝ)
  · exact gammaAnalyticBridge37_witness hn ho hc hGRH hL (le_of_not_ge h36) h37
  by_cases h38 : Real.log n ≤ (18578 / 25 : ℝ)
  · exact gammaAnalyticBridge38_witness hn ho hc hGRH hL (le_of_not_ge h37) h38
  by_cases h39 : Real.log n ≤ (18703 / 25 : ℝ)
  · exact gammaAnalyticBridge39_witness hn ho hc hGRH hL (le_of_not_ge h38) h39
  by_cases h40 : Real.log n ≤ (18828 / 25 : ℝ)
  · exact gammaAnalyticBridge40_witness hn ho hc hGRH hL (le_of_not_ge h39) h40
  by_cases h41 : Real.log n ≤ (18953 / 25 : ℝ)
  · exact gammaAnalyticBridge41_witness hn ho hc hGRH hL (le_of_not_ge h40) h41
  by_cases h42 : Real.log n ≤ (19078 / 25 : ℝ)
  · exact gammaAnalyticBridge42_witness hn ho hc hGRH hL (le_of_not_ge h41) h42
  by_cases h43 : Real.log n ≤ (19203 / 25 : ℝ)
  · exact gammaAnalyticBridge43_witness hn ho hc hGRH hL (le_of_not_ge h42) h43
  by_cases h44 : Real.log n ≤ (19328 / 25 : ℝ)
  · exact gammaAnalyticBridge44_witness hn ho hc hGRH hL (le_of_not_ge h43) h44
  by_cases h45 : Real.log n ≤ (19453 / 25 : ℝ)
  · exact gammaAnalyticBridge45_witness hn ho hc hGRH hL (le_of_not_ge h44) h45
  by_cases h46 : Real.log n ≤ (19578 / 25 : ℝ)
  · exact gammaAnalyticBridge46_witness hn ho hc hGRH hL (le_of_not_ge h45) h46
  by_cases h47 : Real.log n ≤ (19703 / 25 : ℝ)
  · exact gammaAnalyticBridge47_witness hn ho hc hGRH hL (le_of_not_ge h46) h47
  by_cases h48 : Real.log n ≤ (19828 / 25 : ℝ)
  · exact gammaAnalyticBridge48_witness hn ho hc hGRH hL (le_of_not_ge h47) h48
  by_cases h49 : Real.log n ≤ (19953 / 25 : ℝ)
  · exact gammaAnalyticBridge49_witness hn ho hc hGRH hL (le_of_not_ge h48) h49
  by_cases h50 : Real.log n ≤ (20078 / 25 : ℝ)
  · exact gammaAnalyticBridge50_witness hn ho hc hGRH hL (le_of_not_ge h49) h50
  by_cases h51 : Real.log n ≤ (20203 / 25 : ℝ)
  · exact gammaAnalyticBridge51_witness hn ho hc hGRH hL (le_of_not_ge h50) h51
  by_cases h52 : Real.log n ≤ (20328 / 25 : ℝ)
  · exact gammaAnalyticBridge52_witness hn ho hc hGRH hL (le_of_not_ge h51) h52
  by_cases h53 : Real.log n ≤ (20453 / 25 : ℝ)
  · exact gammaAnalyticBridge53_witness hn ho hc hGRH hL (le_of_not_ge h52) h53
  by_cases h54 : Real.log n ≤ (20578 / 25 : ℝ)
  · exact gammaAnalyticBridge54_witness hn ho hc hGRH hL (le_of_not_ge h53) h54
  by_cases h55 : Real.log n ≤ (20703 / 25 : ℝ)
  · exact gammaAnalyticBridge55_witness hn ho hc hGRH hL (le_of_not_ge h54) h55
  by_cases h56 : Real.log n ≤ (20828 / 25 : ℝ)
  · exact gammaAnalyticBridge56_witness hn ho hc hGRH hL (le_of_not_ge h55) h56
  by_cases h57 : Real.log n ≤ (20953 / 25 : ℝ)
  · exact gammaAnalyticBridge57_witness hn ho hc hGRH hL (le_of_not_ge h56) h57
  by_cases h58 : Real.log n ≤ (21078 / 25 : ℝ)
  · exact gammaAnalyticBridge58_witness hn ho hc hGRH hL (le_of_not_ge h57) h58
  by_cases h59 : Real.log n ≤ (21203 / 25 : ℝ)
  · exact gammaAnalyticBridge59_witness hn ho hc hGRH hL (le_of_not_ge h58) h59
  by_cases h60 : Real.log n ≤ (21328 / 25 : ℝ)
  · exact gammaAnalyticBridge60_witness hn ho hc hGRH hL (le_of_not_ge h59) h60
  by_cases h61 : Real.log n ≤ (21453 / 25 : ℝ)
  · exact gammaAnalyticBridge61_witness hn ho hc hGRH hL (le_of_not_ge h60) h61
  by_cases h62 : Real.log n ≤ (21578 / 25 : ℝ)
  · exact gammaAnalyticBridge62_witness hn ho hc hGRH hL (le_of_not_ge h61) h62
  by_cases h63 : Real.log n ≤ (21703 / 25 : ℝ)
  · exact gammaAnalyticBridge63_witness hn ho hc hGRH hL (le_of_not_ge h62) h63
  by_cases h64 : Real.log n ≤ (21828 / 25 : ℝ)
  · exact gammaAnalyticBridge64_witness hn ho hc hGRH hL (le_of_not_ge h63) h64
  by_cases h65 : Real.log n ≤ (21953 / 25 : ℝ)
  · exact gammaAnalyticBridge65_witness hn ho hc hGRH hL (le_of_not_ge h64) h65
  by_cases h66 : Real.log n ≤ (22078 / 25 : ℝ)
  · exact gammaAnalyticBridge66_witness hn ho hc hGRH hL (le_of_not_ge h65) h66
  by_cases h67 : Real.log n ≤ (22203 / 25 : ℝ)
  · exact gammaAnalyticBridge67_witness hn ho hc hGRH hL (le_of_not_ge h66) h67
  by_cases h68 : Real.log n ≤ (22328 / 25 : ℝ)
  · exact gammaAnalyticBridge68_witness hn ho hc hGRH hL (le_of_not_ge h67) h68
  by_cases h69 : Real.log n ≤ (22453 / 25 : ℝ)
  · exact gammaAnalyticBridge69_witness hn ho hc hGRH hL (le_of_not_ge h68) h69
  by_cases h70 : Real.log n ≤ (22578 / 25 : ℝ)
  · exact gammaAnalyticBridge70_witness hn ho hc hGRH hL (le_of_not_ge h69) h70
  by_cases h71 : Real.log n ≤ (22703 / 25 : ℝ)
  · exact gammaAnalyticBridge71_witness hn ho hc hGRH hL (le_of_not_ge h70) h71
  by_cases h72 : Real.log n ≤ (22828 / 25 : ℝ)
  · exact gammaAnalyticBridge72_witness hn ho hc hGRH hL (le_of_not_ge h71) h72
  by_cases h73 : Real.log n ≤ (22953 / 25 : ℝ)
  · exact gammaAnalyticBridge73_witness hn ho hc hGRH hL (le_of_not_ge h72) h73
  by_cases h74 : Real.log n ≤ (23078 / 25 : ℝ)
  · exact gammaAnalyticBridge74_witness hn ho hc hGRH hL (le_of_not_ge h73) h74
  by_cases h75 : Real.log n ≤ (23203 / 25 : ℝ)
  · exact gammaAnalyticBridge75_witness hn ho hc hGRH hL (le_of_not_ge h74) h75
  by_cases h76 : Real.log n ≤ (23328 / 25 : ℝ)
  · exact gammaAnalyticBridge76_witness hn ho hc hGRH hL (le_of_not_ge h75) h76
  by_cases h77 : Real.log n ≤ (23453 / 25 : ℝ)
  · exact gammaAnalyticBridge77_witness hn ho hc hGRH hL (le_of_not_ge h76) h77
  by_cases h78 : Real.log n ≤ (23578 / 25 : ℝ)
  · exact gammaAnalyticBridge78_witness hn ho hc hGRH hL (le_of_not_ge h77) h78
  by_cases h79 : Real.log n ≤ (23703 / 25 : ℝ)
  · exact gammaAnalyticBridge79_witness hn ho hc hGRH hL (le_of_not_ge h78) h79
  by_cases h80 : Real.log n ≤ (23828 / 25 : ℝ)
  · exact gammaAnalyticBridge80_witness hn ho hc hGRH hL (le_of_not_ge h79) h80
  by_cases h81 : Real.log n ≤ (23953 / 25 : ℝ)
  · exact gammaAnalyticBridge81_witness hn ho hc hGRH hL (le_of_not_ge h80) h81
  by_cases h82 : Real.log n ≤ (24078 / 25 : ℝ)
  · exact gammaAnalyticBridge82_witness hn ho hc hGRH hL (le_of_not_ge h81) h82
  by_cases h83 : Real.log n ≤ (24203 / 25 : ℝ)
  · exact gammaAnalyticBridge83_witness hn ho hc hGRH hL (le_of_not_ge h82) h83
  by_cases h84 : Real.log n ≤ (24328 / 25 : ℝ)
  · exact gammaAnalyticBridge84_witness hn ho hc hGRH hL (le_of_not_ge h83) h84
  by_cases h85 : Real.log n ≤ (24453 / 25 : ℝ)
  · exact gammaAnalyticBridge85_witness hn ho hc hGRH hL (le_of_not_ge h84) h85
  by_cases h86 : Real.log n ≤ (24578 / 25 : ℝ)
  · exact gammaAnalyticBridge86_witness hn ho hc hGRH hL (le_of_not_ge h85) h86
  by_cases h87 : Real.log n ≤ (24703 / 25 : ℝ)
  · exact gammaAnalyticBridge87_witness hn ho hc hGRH hL (le_of_not_ge h86) h87
  by_cases h88 : Real.log n ≤ (24828 / 25 : ℝ)
  · exact gammaAnalyticBridge88_witness hn ho hc hGRH hL (le_of_not_ge h87) h88
  by_cases h89 : Real.log n ≤ (24953 / 25 : ℝ)
  · exact gammaAnalyticBridge89_witness hn ho hc hGRH hL (le_of_not_ge h88) h89
  exact gammaAnalyticBridge90_witness hn ho hc hGRH hL (le_of_not_ge h89) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
