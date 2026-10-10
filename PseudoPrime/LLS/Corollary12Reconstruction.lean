/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResidueIntervalCertificates

/-! Five shared analytic intervals for Corollary 1.2.
Regenerate with generate_corollary12_reconstruction.py. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.Corollary12Reconstruction

/-- Checked interval 800 through 20000 for at most 1 prime factors.
The two-term endpoint logarithms, root inequalities and rational gap are
checked in the kernel; the common soundness theorem gives the GRH bound. -/
def interval1 : ResidueIntervalCertificate where
  lower := 800
  upper := 20000
  W := 1
  K := 35
  ja := 10
  jb := 14
  jx := 35
  n := 2
  lo := 667 / 100
  hi := 248 / 25
  h₀ := 400
  s₀ := 2668
  S := 198400
  T := 122 / 5
  roots := fun k ↦
    ([193, 24, 10, 6, 5, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  squareRoots := fun k ↦
    ([14, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  guards := by decide +kernel
  logChecks := by decide +kernel
  rootChecks := by decide +kernel
  gapCheck := by decide +kernel

/-- Under GRH, every unit residue in interval 800 through 20000
with at most 1 distinct prime factors has a least prime below the
totient-log cutoff. Apply the common certificate soundness theorem. -/
theorem leastPrime1 {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (hl : 800 ≤ q) (hu : q ≤ 20000)
    (hw : q.primeFactors.card ≤ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact interval1.leastPrime a hl hu hw hGRH

/-- Checked interval 1300 through 20000 for at most 2 prime factors.
The two-term endpoint logarithms, root inequalities and rational gap are
checked in the kernel; the common soundness theorem gives the GRH bound. -/
def interval2 : ResidueIntervalCertificate where
  lower := 1300
  upper := 20000
  W := 2
  K := 35
  ja := 10
  jb := 14
  jx := 35
  n := 2
  lo := 713 / 100
  hi := 248 / 25
  h₀ := 1300 / 3
  s₀ := 9269 / 3
  S := 198400
  T := 122 / 5
  roots := fun k ↦
    ([213, 25, 10, 6, 5, 4, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  squareRoots := fun k ↦
    ([15, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  guards := by decide +kernel
  logChecks := by decide +kernel
  rootChecks := by decide +kernel
  gapCheck := by decide +kernel

/-- Under GRH, every unit residue in interval 1300 through 20000
with at most 2 distinct prime factors has a least prime below the
totient-log cutoff. Apply the common certificate soundness theorem. -/
theorem leastPrime2 {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (hl : 1300 ≤ q) (hu : q ≤ 20000)
    (hw : q.primeFactors.card ≤ 2) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact interval2.leastPrime a hl hu hw hGRH

/-- Checked interval 2100 through 20000 for at most 3 prime factors.
The two-term endpoint logarithms, root inequalities and rational gap are
checked in the kernel; the common soundness theorem gives the GRH bound. -/
def interval3 : ResidueIntervalCertificate where
  lower := 2100
  upper := 20000
  W := 3
  K := 35
  ja := 11
  jb := 14
  jx := 35
  n := 2
  lo := 191 / 25
  hi := 248 / 25
  h₀ := 560
  s₀ := 21392 / 5
  S := 198400
  T := 122 / 5
  roots := fun k ↦
    ([264, 29, 11, 7, 5, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  squareRoots := fun k ↦
    ([17, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  guards := by decide +kernel
  logChecks := by decide +kernel
  rootChecks := by decide +kernel
  gapCheck := by decide +kernel

/-- Under GRH, every unit residue in interval 2100 through 20000
with at most 3 distinct prime factors has a least prime below the
totient-log cutoff. Apply the common certificate soundness theorem. -/
theorem leastPrime3 {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (hl : 2100 ≤ q) (hu : q ≤ 20000)
    (hw : q.primeFactors.card ≤ 3) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact interval3.leastPrime a hl hu hw hGRH

/-- Checked interval 3300 through 20000 for at most 4 prime factors.
The two-term endpoint logarithms, root inequalities and rational gap are
checked in the kernel; the common soundness theorem gives the GRH bound. -/
def interval4 : ResidueIntervalCertificate where
  lower := 3300
  upper := 20000
  W := 4
  K := 35
  ja := 12
  jb := 14
  jx := 35
  n := 2
  lo := 809 / 100
  hi := 248 / 25
  h₀ := 5280 / 7
  s₀ := 213576 / 35
  S := 198400
  T := 122 / 5
  roots := fun k ↦
    ([334, 33, 13, 7, 5, 4, 4, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  squareRoots := fun k ↦
    ([19, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  guards := by decide +kernel
  logChecks := by decide +kernel
  rootChecks := by decide +kernel
  gapCheck := by decide +kernel

/-- Under GRH, every unit residue in interval 3300 through 20000
with at most 4 distinct prime factors has a least prime below the
totient-log cutoff. Apply the common certificate soundness theorem. -/
theorem leastPrime4 {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (hl : 3300 ≤ q) (hu : q ≤ 20000)
    (hw : q.primeFactors.card ≤ 4) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact interval4.leastPrime a hl hu hw hGRH

/-- Checked interval 5700 through 20000 for at most 5 prime factors.
The two-term endpoint logarithms, root inequalities and rational gap are
checked in the kernel; the common soundness theorem gives the GRH bound. -/
def interval5 : ResidueIntervalCertificate where
  lower := 5700
  upper := 20000
  W := 5
  K := 35
  ja := 13
  jb := 14
  jx := 35
  n := 2
  lo := 861 / 100
  hi := 248 / 25
  h₀ := 91200 / 77
  s₀ := 112176 / 11
  S := 198400
  T := 122 / 5
  roots := fun k ↦
    ([471, 41, 14, 8, 6, 5, 4, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  squareRoots := fun k ↦
    ([22, 7, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List ℕ)[(k - 3) / 2]?.getD 0
  guards := by decide +kernel
  logChecks := by decide +kernel
  rootChecks := by decide +kernel
  gapCheck := by decide +kernel

/-- Under GRH, every unit residue in interval 5700 through 20000
with at most 5 distinct prime factors has a least prime below the
totient-log cutoff. Apply the common certificate soundness theorem. -/
theorem leastPrime5 {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (hl : 5700 ≤ q) (hu : q ≤ 20000)
    (hw : q.primeFactors.card ≤ 5) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact interval5.leastPrime a hl hu hw hGRH

end PseudoPrime.LLS.PaperStatements.Corollary12Reconstruction
