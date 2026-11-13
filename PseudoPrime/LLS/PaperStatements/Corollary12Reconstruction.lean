/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.ResidueIntervalCertificates

/-! Five shared analytic intervals for Corollary 1.2.
Regenerate with generate_corollary12_reconstruction.py. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.Corollary12Reconstruction

/-- Checked interval 800 through 20000 for at most 1 prime factors.
The two-term endpoint logarithms, root inequalities and rational gap are
checked in the kernel; the common soundness theorem gives the GRH bound. -/
private def interval1 : ResidueIntervalCertificate where
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
    match (k - 3) / 2 with
    | 0 => 193
    | 1 => 24
    | 2 => 10
    | 3 => 6
    | 4 => 5
    | 5 => 4
    | 6 => 3
    | 7 => 3
    | 8 => 3
    | 9 => 3
    | 10 => 2
    | 11 => 2
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
  squareRoots := fun k ↦
    match (k - 3) / 2 with
    | 0 => 14
    | 1 => 5
    | 2 => 4
    | 3 => 3
    | 4 => 3
    | 5 => 2
    | 6 => 2
    | 7 => 2
    | 8 => 2
    | 9 => 2
    | 10 => 2
    | 11 => 2
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
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
private def interval2 : ResidueIntervalCertificate where
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
    match (k - 3) / 2 with
    | 0 => 213
    | 1 => 25
    | 2 => 10
    | 3 => 6
    | 4 => 5
    | 5 => 4
    | 6 => 3
    | 7 => 3
    | 8 => 3
    | 9 => 3
    | 10 => 3
    | 11 => 2
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
  squareRoots := fun k ↦
    match (k - 3) / 2 with
    | 0 => 15
    | 1 => 5
    | 2 => 4
    | 3 => 3
    | 4 => 3
    | 5 => 2
    | 6 => 2
    | 7 => 2
    | 8 => 2
    | 9 => 2
    | 10 => 2
    | 11 => 2
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
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
private def interval3 : ResidueIntervalCertificate where
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
    match (k - 3) / 2 with
    | 0 => 264
    | 1 => 29
    | 2 => 11
    | 3 => 7
    | 4 => 5
    | 5 => 4
    | 6 => 4
    | 7 => 3
    | 8 => 3
    | 9 => 3
    | 10 => 3
    | 11 => 2
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
  squareRoots := fun k ↦
    match (k - 3) / 2 with
    | 0 => 17
    | 1 => 6
    | 2 => 4
    | 3 => 3
    | 4 => 3
    | 5 => 2
    | 6 => 2
    | 7 => 2
    | 8 => 2
    | 9 => 2
    | 10 => 2
    | 11 => 2
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
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
private def interval4 : ResidueIntervalCertificate where
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
    match (k - 3) / 2 with
    | 0 => 334
    | 1 => 33
    | 2 => 13
    | 3 => 7
    | 4 => 5
    | 5 => 4
    | 6 => 4
    | 7 => 3
    | 8 => 3
    | 9 => 3
    | 10 => 3
    | 11 => 3
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
  squareRoots := fun k ↦
    match (k - 3) / 2 with
    | 0 => 19
    | 1 => 6
    | 2 => 4
    | 3 => 3
    | 4 => 3
    | 5 => 2
    | 6 => 2
    | 7 => 2
    | 8 => 2
    | 9 => 2
    | 10 => 2
    | 11 => 2
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
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
private def interval5 : ResidueIntervalCertificate where
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
    match (k - 3) / 2 with
    | 0 => 471
    | 1 => 41
    | 2 => 14
    | 3 => 8
    | 4 => 6
    | 5 => 5
    | 6 => 4
    | 7 => 3
    | 8 => 3
    | 9 => 3
    | 10 => 3
    | 11 => 3
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
  squareRoots := fun k ↦
    match (k - 3) / 2 with
    | 0 => 22
    | 1 => 7
    | 2 => 4
    | 3 => 3
    | 4 => 3
    | 5 => 3
    | 6 => 2
    | 7 => 2
    | 8 => 2
    | 9 => 2
    | 10 => 2
    | 11 => 2
    | 12 => 2
    | 13 => 2
    | 14 => 2
    | 15 => 2
    | 16 => 2
    | _ => 0
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
