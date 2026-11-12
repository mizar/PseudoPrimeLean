/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta32768to33024
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta33024to33280
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta33280to33536
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta33536to33792
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta33792to34048
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta34048to34304
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta34304to34560
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta34560to34816
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta34816to35072
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta35072to35328
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta35328to35584
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta35584to35840
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta35840to36096
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta36096to36352
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta36352to36608
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta36608to36864
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta36864to37120
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta37120to37376
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta37376to37632
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta37632to37888
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta37888to38144
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta38144to38400
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta38400to38656
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta38656to38912
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta38912to39168
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta39168to39424
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta39424to39680
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta39680to39760

/-! # Lee–Nosal theta error bound from 32768 to 39760 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The unconditional Lee–Nosal theta error bound on `[32768, 39760]` follows by
combining independent interval theorems without importing their numerical certificates. -/
theorem theta_lee_nosal_32768_39760 {x : ℝ} (ha : 32768 ≤ x) (hb : x ≤ 39760) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h33024 : x ≤ 33024
  · exact theta_lee_nosal_32768_33024 ha h33024
  by_cases h33280 : x ≤ 33280
  · exact theta_lee_nosal_33024_33280 (by linarith only [h33024]) h33280
  by_cases h33536 : x ≤ 33536
  · exact theta_lee_nosal_33280_33536 (by linarith only [h33280]) h33536
  by_cases h33792 : x ≤ 33792
  · exact theta_lee_nosal_33536_33792 (by linarith only [h33536]) h33792
  by_cases h34048 : x ≤ 34048
  · exact theta_lee_nosal_33792_34048 (by linarith only [h33792]) h34048
  by_cases h34304 : x ≤ 34304
  · exact theta_lee_nosal_34048_34304 (by linarith only [h34048]) h34304
  by_cases h34560 : x ≤ 34560
  · exact theta_lee_nosal_34304_34560 (by linarith only [h34304]) h34560
  by_cases h34816 : x ≤ 34816
  · exact theta_lee_nosal_34560_34816 (by linarith only [h34560]) h34816
  by_cases h35072 : x ≤ 35072
  · exact theta_lee_nosal_34816_35072 (by linarith only [h34816]) h35072
  by_cases h35328 : x ≤ 35328
  · exact theta_lee_nosal_35072_35328 (by linarith only [h35072]) h35328
  by_cases h35584 : x ≤ 35584
  · exact theta_lee_nosal_35328_35584 (by linarith only [h35328]) h35584
  by_cases h35840 : x ≤ 35840
  · exact theta_lee_nosal_35584_35840 (by linarith only [h35584]) h35840
  by_cases h36096 : x ≤ 36096
  · exact theta_lee_nosal_35840_36096 (by linarith only [h35840]) h36096
  by_cases h36352 : x ≤ 36352
  · exact theta_lee_nosal_36096_36352 (by linarith only [h36096]) h36352
  by_cases h36608 : x ≤ 36608
  · exact theta_lee_nosal_36352_36608 (by linarith only [h36352]) h36608
  by_cases h36864 : x ≤ 36864
  · exact theta_lee_nosal_36608_36864 (by linarith only [h36608]) h36864
  by_cases h37120 : x ≤ 37120
  · exact theta_lee_nosal_36864_37120 (by linarith only [h36864]) h37120
  by_cases h37376 : x ≤ 37376
  · exact theta_lee_nosal_37120_37376 (by linarith only [h37120]) h37376
  by_cases h37632 : x ≤ 37632
  · exact theta_lee_nosal_37376_37632 (by linarith only [h37376]) h37632
  by_cases h37888 : x ≤ 37888
  · exact theta_lee_nosal_37632_37888 (by linarith only [h37632]) h37888
  by_cases h38144 : x ≤ 38144
  · exact theta_lee_nosal_37888_38144 (by linarith only [h37888]) h38144
  by_cases h38400 : x ≤ 38400
  · exact theta_lee_nosal_38144_38400 (by linarith only [h38144]) h38400
  by_cases h38656 : x ≤ 38656
  · exact theta_lee_nosal_38400_38656 (by linarith only [h38400]) h38656
  by_cases h38912 : x ≤ 38912
  · exact theta_lee_nosal_38656_38912 (by linarith only [h38656]) h38912
  by_cases h39168 : x ≤ 39168
  · exact theta_lee_nosal_38912_39168 (by linarith only [h38912]) h39168
  by_cases h39424 : x ≤ 39424
  · exact theta_lee_nosal_39168_39424 (by linarith only [h39168]) h39424
  by_cases h39680 : x ≤ 39680
  · exact theta_lee_nosal_39424_39680 (by linarith only [h39424]) h39680
  exact theta_lee_nosal_39680_39760 (by linarith only [h39680]) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
