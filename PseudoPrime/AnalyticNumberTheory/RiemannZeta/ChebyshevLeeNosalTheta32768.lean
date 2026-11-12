/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta16384
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta16384to18085
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta18085to19472
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta19472to20880
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta20880to22356
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta22356to24376
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta24376to26035
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta26035to27692
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta27692to29176
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta29176to30667
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta30667to31785
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta31785to32527
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta32527to32768

/-! # Cumulative Lee–Nosal theta bound through 32768 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent theta certificates give the Lee–Nosal estimate on `[2657, 32768)`. -/
theorem theta_lee_nosal_2657_32768 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 32768) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h0 : x < 16384
  · exact theta_lee_nosal_2657_16384 ha h0
  by_cases h1 : x < 18085
  · exact theta_lee_nosal_16384_18085 (le_of_not_gt h0) h1
  by_cases h2 : x < 19472
  · exact theta_lee_nosal_18085_19472 (le_of_not_gt h1) h2
  by_cases h3 : x < 20880
  · exact theta_lee_nosal_19472_20880 (le_of_not_gt h2) h3
  by_cases h4 : x < 22356
  · exact theta_lee_nosal_20880_22356 (le_of_not_gt h3) h4
  by_cases h5 : x < 24376
  · exact theta_lee_nosal_22356_24376 (le_of_not_gt h4) h5
  by_cases h6 : x < 26035
  · exact theta_lee_nosal_24376_26035 (le_of_not_gt h5) h6
  by_cases h7 : x < 27692
  · exact theta_lee_nosal_26035_27692 (le_of_not_gt h6) h7
  by_cases h8 : x < 29176
  · exact theta_lee_nosal_27692_29176 (le_of_not_gt h7) h8
  by_cases h9 : x < 30667
  · exact theta_lee_nosal_29176_30667 (le_of_not_gt h8) h9
  by_cases h10 : x < 31785
  · exact theta_lee_nosal_30667_31785 (le_of_not_gt h9) h10
  by_cases h11 : x < 32527
  · exact theta_lee_nosal_31785_32527 (le_of_not_gt h10) h11
  · exact theta_lee_nosal_32527_32768 (le_of_not_gt h11) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
