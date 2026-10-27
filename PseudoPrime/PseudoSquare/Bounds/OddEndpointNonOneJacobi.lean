/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointElementaryCosts
public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic
public import PseudoPrime.NumberTheory.JacobiWitness.Existence

/-! # Odd-prime non-one Jacobi witnesses from two-power endpoint costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For odd nonsquare n under GRH, 64<=Y<=x and negative odd endpoint limit
at the canonical primitive conductor, an odd prime p<=x has Jacobi(n,p) different
from one. Apply the odd character witness theorem. If p divides n the Jacobi
value is zero; otherwise transfer the primitive value. No exclusion of n's
prime factors or arithmetic bridge is assumed. This is not a negative-witness claim. -/
theorem exists_odd_prime_jacobi_ne_one_of_oddEndpointLimit_neg {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim :
      LLS.PaperStatements.oddEndpointLimit (NumberTheory.complexQuadraticCharacter n hn).conductor x
          Y <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p ≠ 1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  let _ : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero⟩
  let χ := NumberTheory.primitiveQuadraticCharacter n hn
  have hp : χ.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive (NumberTheory.complexQuadraticCharacter n hn)
  have hne : χ ≠ 1 := NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
  have hq : 2 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (Nat.two_le_iff _).mpr ⟨NeZero.ne _, fun he ↦ hne (DirichletCharacter.level_one' χ he)⟩
  obtain ⟨p, hprime, hodd, hpx, hv⟩ :=
    LLS.PaperStatements.exists_odd_prime_not_one_of_oddEndpointLimit_neg hq hGRH hp hne
      (fun hi ↦ hne (inv_eq_one.mp hi)) hx hY hYx hlim
  by_cases hpn : p ∣ n
  · have hm := NumberTheory.primeNeOneWitness_mem_of_dvd hprime hodd hpn
    exact ⟨p, hprime, hodd, hpx, hm.2.2⟩
  · have he := NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hprime hodd hpn
    simp only [Int.cast_natCast] at he
    have hj : jacobiSym n p ≠ 1 := by
      intro hj
      rw [hj, Int.cast_one] at he
      exact hv he
    exact ⟨p, hprime, hodd, hpx, hj⟩

/-- Under the same odd-nonsquare GRH and endpoint-limit assumptions, the least
odd-prime non-one Jacobi witness is at most x after real casting. The nonempty
set argument defines the existing least-witness function. Obtain an actual witness
and apply leastness. No corresponding negative-witness conclusion is inferred. -/
theorem primeNeOneWitness_cast_le_of_oddEndpointLimit_neg {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim :
      LLS.PaperStatements.oddEndpointLimit (NumberTheory.complexQuadraticCharacter n hn).conductor x
          Y <
        0)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_of_oddEndpointLimit_neg hn hns hGRH hx hY hYx hlim
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- For odd nonsquare n under GRH and 64<=Y<=x, a negative elementary odd
endpoint limit evaluated at 4*n yields an odd non-one Jacobi prime at most x.
Bound the canonical conductor by 4*n using monotonicity and apply the exact
criterion. No finite sums, conductor calculation or factorization is required. -/
theorem exists_odd_prime_jacobi_ne_one_of_oddEndpointElementaryLimit_neg {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim : LLS.PaperStatements.oddEndpointElementaryLimit (4 * n) x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p ≠ 1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  have hq0 := Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero
  have hqle :=
    Nat.le_of_dvd (NeZero.pos (4 * n))
      (NumberTheory.complexQuadraticCharacter n hn).conductor_dvd_level
  have hm := LLS.PaperStatements.oddEndpointElementaryLimit_mono_level hq0 hqle hx.le hY
  have hy0 : 0 < Y := by linarith only [hY]
  have he :=
    LLS.PaperStatements.oddEndpointLimit_le_elementary
      (NumberTheory.complexQuadraticCharacter n hn).conductor hx.le hy0
  exact
    exists_odd_prime_jacobi_ne_one_of_oddEndpointLimit_neg hn hns hGRH hx hY hYx
      ((he.trans hm).trans_lt hlim)

/-- Under the same elementary odd endpoint condition at 4*n, the least odd-prime
non-one Jacobi witness is at most x. The nonempty-set argument supplies the public
least-witness definition. Apply leastness to the actual prime from the elementary
criterion. Zero-valued witnesses are included. -/
theorem primeNeOneWitness_cast_le_of_oddEndpointElementaryLimit_neg {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim : LLS.PaperStatements.oddEndpointElementaryLimit (4 * n) x Y < 0)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_of_oddEndpointElementaryLimit_neg hn hns hGRH hx hY hYx hlim
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

end PseudoPrime.PseudoSquare
