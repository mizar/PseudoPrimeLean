/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.DigammaRationalCertificate
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorPrefixBounds
public import PseudoPrime.Analysis.PrecisePiLogBound
public import PseudoPrime.Analysis.GammaResolventCertificate

/-! # Signed real Gamma contributions at the certified resolvent nodes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- Input: the fixed signed nodes and parity shift 0.
Claim: their real digamma-minus-log-pi combination is at most -15709/10000.
Proof: eight short rational digamma intervals and the certified lower log-pi bound.
Role: preserve cancellation when bounding the signed archimedean contribution. -/
theorem signed_digamma_0_le_precise :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 0) / 2) : ℂ)).re -
                  Real.log Real.pi) /
                2))).sum ≤
      -(15709 / 10000 : ℝ) := by
  have h0 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (21 / 40) 8 3 8 (-1851 / 1000) (-1839 / 1000) = true by
        decide +kernel)
  have h1 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (13 / 20) 8 3 8 (-1381 / 1000) (-1369 / 1000) = true by
        decide +kernel)
  have h2 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (3 / 4) 8 3 8 (-1091 / 1000) (-1079 / 1000) = true by
        decide +kernel)
  have h3 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (11 / 10) 8 3 8 (-431 / 1000) (-419 / 1000) = true by
        decide +kernel)
  have h4 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (7 / 5) 8 3 8 (-71 / 1000) (-59 / 1000) = true by
        decide +kernel)
  have h5 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (37 / 20) 8 3 8 (319 / 1000) (331 / 1000) = true by
        decide +kernel)
  have h6 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (5 / 2) 8 3 8 (699 / 1000) (711 / 1000) = true by
        decide +kernel)
  have h7 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (15 / 4) 8 4 8 (1179 / 1000) (1191 / 1000) = true by
        decide +kernel)
  norm_num only [Analysis.gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_one, zero_mul,
    add_zero] at ⊢ h0 h1 h2 h3 h4 h5 h6 h7
  linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2,
    h7.1, h7.2, Analysis.log_pi_ge_2096_div_1831]

/-- For the fixed even nodes, the precise signed Gamma bound implies -3/2.
Apply rational monotonicity. Role: preserve the existing coarse interface. -/
theorem signed_digamma_0_le :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 0) / 2) : ℂ)).re -
                  Real.log Real.pi) /
                2))).sum ≤
      -3 / 2 := by
  exact signed_digamma_0_le_precise.trans (by norm_num only)

/-- Input: the fixed signed nodes and parity shift 1.
Claim: their real digamma-minus-log-pi combination is at most -4/5.
Proof: eight short rational digamma intervals and the certified lower log-pi bound.
Role: preserve cancellation when bounding the signed archimedean contribution. -/
theorem signed_digamma_1_le :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 1) / 2) : ℂ)).re -
                  Real.log Real.pi) /
                2))).sum ≤
      -4 / 5 := by
  have h0 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (41 / 40) 8 3 8 (-541 / 1000) (-529 / 1000) = true by
        decide +kernel)
  have h1 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (23 / 20) 8 3 8 (-361 / 1000) (-349 / 1000) = true by
        decide +kernel)
  have h2 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (5 / 4) 8 3 8 (-231 / 1000) (-219 / 1000) = true by
        decide +kernel)
  have h3 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (8 / 5) 8 3 8 (119 / 1000) (131 / 1000) = true by
        decide +kernel)
  have h4 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (19 / 10) 8 3 8 (349 / 1000) (361 / 1000) = true by
        decide +kernel)
  have h5 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (47 / 20) 8 3 8 (619 / 1000) (631 / 1000) = true by
        decide +kernel)
  have h6 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (3) 8 3 8 (919 / 1000) (931 / 1000) = true by
        decide +kernel)
  have h7 :=
    rationalDigammaIntervalCheck_sound
      (show rationalDigammaIntervalCheck (17 / 4) 8 4 8 (1319 / 1000) (1331 / 1000) = true by
        decide +kernel)
  norm_num only [Analysis.gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_one, zero_mul,
    add_zero] at ⊢ h0 h1 h2 h3 h4 h5 h6 h7
  linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2,
    h7.1, h7.2, Analysis.log_pi_ge_2096_div_1831]

end PseudoPrime.AnalyticNumberTheory.Gamma
