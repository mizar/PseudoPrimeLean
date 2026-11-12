/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta39760
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta40000
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta40312to40512
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta40512to40778
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta40778to41011
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta41011to41024
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta41024to41277
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta41277to41536
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta41536to41797
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta41797to42048
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta42048to42372
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta42372to42560
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta42560to42816
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta42816to43072
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta43072to43491
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta43491to43584
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta43584to43897
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta43897to44096
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta44096to44421
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta44421to44608
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta44608to44918
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta44918to45120
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta45120to45422
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta45422to45632
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta45632to45926
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta45926to46144
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta46144to46398
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta46398to46634
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta46634to46656
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta46656to46913
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta46913to47168
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta47168to47408
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta47408to47634
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta47634to47680
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta47680to47914
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta47914to48162
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta48162to48192
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta48192to48421
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta48421to48637
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta48637to48704
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta48704to48928
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta48928to49165
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta49165to49216
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta49216to49489
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta49489to49728
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta49728to49987
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta49987to50000

/-! # Finite Lee–Nosal theta error bound through 50000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal theta error bound holds unconditionally on `[40000, 50000]`.
Independent interval theorems are combined without exposing endpoint certificates. -/
theorem theta_lee_nosal_40000_50000 {x : ℝ} (ha : 40000 ≤ x) (hb : x ≤ 50000) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h40312 : x ≤ 40312
  · exact theta_lee_nosal_40000_40312 ha h40312
  by_cases h40512 : x ≤ 40512
  · exact theta_lee_nosal_40312_40512 (by linarith only [h40312]) h40512
  by_cases h40778 : x ≤ 40778
  · exact theta_lee_nosal_40512_40778 (by linarith only [h40512]) h40778
  by_cases h41011 : x ≤ 41011
  · exact theta_lee_nosal_40778_41011 (by linarith only [h40778]) h41011
  by_cases h41024 : x ≤ 41024
  · exact theta_lee_nosal_41011_41024 (by linarith only [h41011]) h41024
  by_cases h41277 : x ≤ 41277
  · exact theta_lee_nosal_41024_41277 (by linarith only [h41024]) h41277
  by_cases h41536 : x ≤ 41536
  · exact theta_lee_nosal_41277_41536 (by linarith only [h41277]) h41536
  by_cases h41797 : x ≤ 41797
  · exact theta_lee_nosal_41536_41797 (by linarith only [h41536]) h41797
  by_cases h42048 : x ≤ 42048
  · exact theta_lee_nosal_41797_42048 (by linarith only [h41797]) h42048
  by_cases h42372 : x ≤ 42372
  · exact theta_lee_nosal_42048_42372 (by linarith only [h42048]) h42372
  by_cases h42560 : x ≤ 42560
  · exact theta_lee_nosal_42372_42560 (by linarith only [h42372]) h42560
  by_cases h42816 : x ≤ 42816
  · exact theta_lee_nosal_42560_42816 (by linarith only [h42560]) h42816
  by_cases h43072 : x ≤ 43072
  · exact theta_lee_nosal_42816_43072 (by linarith only [h42816]) h43072
  by_cases h43491 : x ≤ 43491
  · exact theta_lee_nosal_43072_43491 (by linarith only [h43072]) h43491
  by_cases h43584 : x ≤ 43584
  · exact theta_lee_nosal_43491_43584 (by linarith only [h43491]) h43584
  by_cases h43897 : x ≤ 43897
  · exact theta_lee_nosal_43584_43897 (by linarith only [h43584]) h43897
  by_cases h44096 : x ≤ 44096
  · exact theta_lee_nosal_43897_44096 (by linarith only [h43897]) h44096
  by_cases h44421 : x ≤ 44421
  · exact theta_lee_nosal_44096_44421 (by linarith only [h44096]) h44421
  by_cases h44608 : x ≤ 44608
  · exact theta_lee_nosal_44421_44608 (by linarith only [h44421]) h44608
  by_cases h44918 : x ≤ 44918
  · exact theta_lee_nosal_44608_44918 (by linarith only [h44608]) h44918
  by_cases h45120 : x ≤ 45120
  · exact theta_lee_nosal_44918_45120 (by linarith only [h44918]) h45120
  by_cases h45422 : x ≤ 45422
  · exact theta_lee_nosal_45120_45422 (by linarith only [h45120]) h45422
  by_cases h45632 : x ≤ 45632
  · exact theta_lee_nosal_45422_45632 (by linarith only [h45422]) h45632
  by_cases h45926 : x ≤ 45926
  · exact theta_lee_nosal_45632_45926 (by linarith only [h45632]) h45926
  by_cases h46144 : x ≤ 46144
  · exact theta_lee_nosal_45926_46144 (by linarith only [h45926]) h46144
  by_cases h46398 : x ≤ 46398
  · exact theta_lee_nosal_46144_46398 (by linarith only [h46144]) h46398
  by_cases h46634 : x ≤ 46634
  · exact theta_lee_nosal_46398_46634 (by linarith only [h46398]) h46634
  by_cases h46656 : x ≤ 46656
  · exact theta_lee_nosal_46634_46656 (by linarith only [h46634]) h46656
  by_cases h46913 : x ≤ 46913
  · exact theta_lee_nosal_46656_46913 (by linarith only [h46656]) h46913
  by_cases h47168 : x ≤ 47168
  · exact theta_lee_nosal_46913_47168 (by linarith only [h46913]) h47168
  by_cases h47408 : x ≤ 47408
  · exact theta_lee_nosal_47168_47408 (by linarith only [h47168]) h47408
  by_cases h47634 : x ≤ 47634
  · exact theta_lee_nosal_47408_47634 (by linarith only [h47408]) h47634
  by_cases h47680 : x ≤ 47680
  · exact theta_lee_nosal_47634_47680 (by linarith only [h47634]) h47680
  by_cases h47914 : x ≤ 47914
  · exact theta_lee_nosal_47680_47914 (by linarith only [h47680]) h47914
  by_cases h48162 : x ≤ 48162
  · exact theta_lee_nosal_47914_48162 (by linarith only [h47914]) h48162
  by_cases h48192 : x ≤ 48192
  · exact theta_lee_nosal_48162_48192 (by linarith only [h48162]) h48192
  by_cases h48421 : x ≤ 48421
  · exact theta_lee_nosal_48192_48421 (by linarith only [h48192]) h48421
  by_cases h48637 : x ≤ 48637
  · exact theta_lee_nosal_48421_48637 (by linarith only [h48421]) h48637
  by_cases h48704 : x ≤ 48704
  · exact theta_lee_nosal_48637_48704 (by linarith only [h48637]) h48704
  by_cases h48928 : x ≤ 48928
  · exact theta_lee_nosal_48704_48928 (by linarith only [h48704]) h48928
  by_cases h49165 : x ≤ 49165
  · exact theta_lee_nosal_48928_49165 (by linarith only [h48928]) h49165
  by_cases h49216 : x ≤ 49216
  · exact theta_lee_nosal_49165_49216 (by linarith only [h49165]) h49216
  by_cases h49489 : x ≤ 49489
  · exact theta_lee_nosal_49216_49489 (by linarith only [h49216]) h49489
  by_cases h49728 : x ≤ 49728
  · exact theta_lee_nosal_49489_49728 (by linarith only [h49489]) h49728
  by_cases h49987 : x ≤ 49987
  · exact theta_lee_nosal_49728_49987 (by linarith only [h49728]) h49987
  exact theta_lee_nosal_49987_50000 (by linarith only [h49987]) hb

/-- The Lee–Nosal theta error bound holds unconditionally on `[39760, 50000]`.
The lower connecting interval and the previously combined interval cover this range. -/
theorem theta_lee_nosal_39760_50000 {x : ℝ} (ha : 39760 ≤ x) (hb : x ≤ 50000) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x ≤ 40000
  · exact theta_lee_nosal_39760_40000 ha h
  · exact theta_lee_nosal_40000_50000 (le_of_not_ge h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
