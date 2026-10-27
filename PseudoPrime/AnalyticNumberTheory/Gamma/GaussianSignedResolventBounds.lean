/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.SignedResolventBounds
public import PseudoPrime.Analysis.GaussianResolventCertificate

/-! # Signed Gaussian archimedean contributions -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The signed Gaussian digamma contribution at parity 0 is bounded by
-36 / 25. Small rational enclosures preserve all coefficient signs. -/
theorem gaussian_signed_digamma_0_le :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 0) / 2) : ℂ)).re -
                  Real.log Real.pi) /
                2))).sum ≤
      -36 / 25 := by
  have h0 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (21 / 40) 16 4 12 (-18454 / 10000) (-18448 / 10000) = true
        by decide +kernel)
  have h1 :=
    rationalDigammaIntervalCheck_sound
      (show
        rationalDigammaIntervalCheck (239 / 400) 16 4 12 (-15499 / 10000) (-15494 / 10000) = true by
        decide +kernel)
  have h2 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (11 / 16) 16 4 12 (-12562 / 10000) (-12556 / 10000) = true
        by decide +kernel)
  have h3 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (4 / 5) 16 4 12 (-9652 / 10000) (-9647 / 10000) = true by
        decide +kernel)
  have h4 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (377 / 400) 16 4 12 (-6762 / 10000) (-6757 / 10000) = true
        by decide +kernel)
  have h5 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (9 / 8) 16 4 12 (-3887 / 10000) (-3882 / 10000) = true by
        decide +kernel)
  have h6 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (541 / 400) 16 4 12 (-1114 / 10000) (-1109 / 10000) = true
        by decide +kernel)
  have h7 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (131 / 80) 16 4 12 (1576 / 10000) (1581 / 10000) = true by
        decide +kernel)
  have h8 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (2) 16 4 12 (4226 / 10000) (4231 / 10000) = true by
        decide +kernel)
  have h9 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (491 / 200) 16 4 12 (6807 / 10000) (6811 / 10000) = true by
        decide +kernel)
  have h10 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (1211 / 400) 16 4 12 (9334 / 10000) (9339 / 10000) = true
        by decide +kernel)
  have h11 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (15 / 4) 16 4 12 (11824 / 10000) (11828 / 10000) = true by
        decide +kernel)
  norm_num only [Analysis.gaussianResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_one, zero_mul,
    add_zero] at ⊢ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2,
    h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2, h11.1, h11.2,
    Analysis.log_pi_ge_2096_div_1831]

/-- The signed Gaussian digamma contribution at parity 1 is bounded by
-789 / 1000. Small rational enclosures preserve all coefficient signs. -/
theorem gaussian_signed_digamma_1_le :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 1) / 2) : ℂ)).re -
                  Real.log Real.pi) /
                2))).sum ≤
      -789 / 1000 := by
  have h0 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (41 / 40) 16 4 12 (-5370 / 10000) (-5365 / 10000) = true by
        decide +kernel)
  have h1 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (439 / 400) 16 4 12 (-4275 / 10000) (-4270 / 10000) = true
        by decide +kernel)
  have h2 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (19 / 16) 16 4 12 (-3052 / 10000) (-3047 / 10000) = true by
        decide +kernel)
  have h3 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (13 / 10) 16 4 12 (-1694 / 10000) (-1689 / 10000) = true by
        decide +kernel)
  have h4 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (577 / 400) 16 4 12 (-189 / 10000) (-184 / 10000) = true by
        decide +kernel)
  have h5 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (13 / 8) 16 4 12 (1471 / 10000) (1476 / 10000) = true by
        decide +kernel)
  have h6 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (741 / 400) 16 4 12 (3228 / 10000) (3233 / 10000) = true by
        decide +kernel)
  have h7 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (171 / 80) 16 4 12 (5077 / 10000) (5081 / 10000) = true by
        decide +kernel)
  have h8 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (5 / 2) 16 4 12 (7030 / 10000) (7035 / 10000) = true by
        decide +kernel)
  have h9 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (591 / 200) 16 4 12 (9047 / 10000) (9051 / 10000) = true by
        decide +kernel)
  have h10 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (1411 / 400) 16 4 12 (11120 / 10000) (11125 / 10000) = true
        by decide +kernel)
  have h11 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (17 / 4) 16 4 12 (13245 / 10000) (13249 / 10000) = true by
        decide +kernel)
  norm_num only [Analysis.gaussianResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_one, zero_mul,
    add_zero] at ⊢ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2,
    h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2, h11.1, h11.2,
    Analysis.log_pi_ge_2096_div_1831]

end PseudoPrime.AnalyticNumberTheory.Gamma
