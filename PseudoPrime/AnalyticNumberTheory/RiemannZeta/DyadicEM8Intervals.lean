/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComputedComplexIntervals
public import PseudoPrime.Analysis.ReciprocalSqrtIntervals
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicPowerSums
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicEM8

/-! # Computed intervals for the cumulative odd-power recurrence -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- If positive natural bases multiply to `n`, certified rectangles for their critical-power
terms give a computed rectangle for the term at `n`. This is the sound step for generating
composite odd terms from earlier factors; acyclicity of a particular factor certificate must
be checked separately by its consumer. -/
theorem factoredTerm_contains (G : ℤ) (A B : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (s : ℂ) (a b n : ℕ) (hG : 0 < G) (ha : 0 < a) (hb : 0 < b) (hab : a * b = n)
    (hA : Analysis.complexIntervalContains A.1 A.2 G (dyadicPowerTerm s a))
    (hB : Analysis.complexIntervalContains B.1 B.2 G (dyadicPowerTerm s b)) :
    Analysis.complexIntervalContains (Analysis.roundedComplexProduct G A B).1
      (Analysis.roundedComplexProduct G A B).2 G (dyadicPowerTerm s n) := by
  rw [← hab, dyadicPowerTerm_mul s a b ha hb]
  exact Analysis.roundedComplexProduct_contains hG hA hB

/-- A family of critical-power rectangles is sound on a specified set of positive bases up to
`N` when each is certified directly or is the product of two smaller bases in the same set.
Strong induction proves that the factor references are acyclic. Choosing the odd bases permits
a certificate to avoid even composite terms, indexed list access, and primality hypotheses. -/
theorem factoredFamily_contains (G : ℤ)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (s : ℂ) (N : ℕ) (P : ℕ → Prop)
    (hG : 0 < G)
    (hstep :
      ∀ n,
        P n →
          0 < n →
          n ≤ N →
          Analysis.complexIntervalContains (B n).1 (B n).2 G (dyadicPowerTerm s n) ∨
            ∃ a b,
              P a ∧
                P b ∧
                0 < a ∧
                0 < b ∧
                a < n ∧ b < n ∧ a * b = n ∧ B n = Analysis.roundedComplexProduct G (B a) (B b)) :
    ∀ n,
      P n →
        0 < n →
        n ≤ N → Analysis.complexIntervalContains (B n).1 (B n).2 G (dyadicPowerTerm s n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hP hn hN
    rcases hstep n hP hn hN with h | ⟨a, b, hPa, hPb, ha, hb, han, hbn, hab, hbox⟩
    · exact h
    · rw [hbox]
      exact
        factoredTerm_contains G (B a) (B b) s a b n hG ha hb hab
          (ih a han hPa ha (Nat.le_trans (Nat.le_of_lt han) hN))
          (ih b hbn hPb hb (Nat.le_trans (Nat.le_of_lt hbn) hN))

/-- Compute a rectangle for a critical-line power term from a reciprocal-square-root amplitude
interval and a complex phase rectangle. The scale is shared by both inputs; a zero imaginary
amplitude and outward-rounded complex multiplication produce the result. -/
def criticalTermBox (G : ℤ) (A : Analysis.IntegerInterval)
    (P : Analysis.IntegerInterval × Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  Analysis.roundedComplexProduct G (A, ⟨0, 0⟩) P

/-- For a positive integer base, certified reciprocal-square-root and phase intervals enclose
the corresponding critical-line power term. The positive-base amplitude-phase identity and
computed complex multiplication prove this interface for each odd term and the base-two term. -/
theorem criticalTermBox_contains (G : ℤ) (A : Analysis.IntegerInterval)
    (P : Analysis.IntegerInterval × Analysis.IntegerInterval) (n : ℕ) (t : ℝ) (hG : 0 < G)
    (hn : 0 < n) (ha : A.Contains G (Real.sqrt n)⁻¹)
    (hp :
      Analysis.complexIntervalContains P.1 P.2 G
        (Complex.exp (((-t * Real.log n : ℝ) : ℂ) * Complex.I))) :
    Analysis.complexIntervalContains (criticalTermBox G A P).1 (criticalTermBox G A P).2 G
      (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) n) := by
  have hA : Analysis.complexIntervalContains A ⟨0, 0⟩ G (((Real.sqrt n)⁻¹ : ℝ) : ℂ) := by
    constructor
    · simpa only [Complex.ofReal_re] using ha
    · simp only [Complex.ofReal_im, Analysis.IntegerInterval.Contains, Int.cast_zero, zero_div,
        le_refl, and_self]
  have h := Analysis.roundedComplexProduct_contains (A := (A, ⟨0, 0⟩)) (B := P) hG hA hp
  have hreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [dyadicPowerTerm, ite_eq_right (Nat.ne_of_gt hn), ← Complex.ofReal_natCast,
    critical_power_sqrt_phase _ _ hreal, ← Complex.ofReal_inv]
  exact h

/-- A positive integer base interval, checked square-root and reciprocal intervals, and a
certified phase rectangle enclose the corresponding critical-line power term. The integer checks
discharge the amplitude-containment hypothesis, allowing the same amplitude certificate to be
shared by different endpoint phases. -/
theorem criticalTermBox_checked (G : ℤ) (N S A : Analysis.IntegerInterval)
    (P : Analysis.IntegerInterval × Analysis.IntegerInterval) (n : ℕ) (t : ℝ) (hG : 0 < G)
    (hn : 0 < n) (hN : N.Contains G n)
    (hs : Analysis.integerSqrtCheck G N.lower N.upper S.lower S.upper = true)
    (ha : Analysis.integerReciprocalCheck G S.lower S.upper A.lower A.upper = true)
    (hp :
      Analysis.complexIntervalContains P.1 P.2 G
        (Complex.exp (((-t * Real.log n : ℝ) : ℂ) * Complex.I))) :
    Analysis.complexIntervalContains (criticalTermBox G A P).1 (criticalTermBox G A P).2 G
      (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) n) := by
  exact criticalTermBox_contains G A P n t hG hn (Analysis.reciprocal_sqrt_contains hN hs ha) hp

/-- A successful shared amplitude witness and a certified phase rectangle enclose one
critical-line power term. The witness depends only on the positive integer base and scale, so
the same check can supply both endpoints and multiple candidate zero intervals. -/
theorem criticalTermBox_witness (G : ℤ) (w : Analysis.AmplitudeWitness)
    (P : Analysis.IntegerInterval × Analysis.IntegerInterval) (n : ℕ) (t : ℝ) (hG : 0 < G)
    (hn : 0 < n) (hw : w.check G n = true)
    (hp :
      Analysis.complexIntervalContains P.1 P.2 G
        (Complex.exp (((-t * Real.log n : ℝ) : ℂ) * Complex.I))) :
    Analysis.complexIntervalContains (criticalTermBox G w.inverse P).1
      (criticalTermBox G w.inverse P).2 G
      (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) n) := by
  exact criticalTermBox_contains G w.inverse P n t hG hn (w.sound G n hG hw) hp

/-- Sum the rectangles of the odd terms in the next dyadic block, using a function that supplies
the rectangle for each positive integer. The two coordinates use exact finite sums of integer
endpoints. This block feeds the cumulative odd-prefix evaluator without list indexing. -/
def dyadicOddBlockBox (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (m : ℕ) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  (Analysis.intervalFinsetSum (Finset.range (2 ^ m)) (fun k ↦ (B (2 * (2 ^ m + k) + 1)).1),
    Analysis.intervalFinsetSum (Finset.range (2 ^ m)) (fun k ↦ (B (2 * (2 ^ m + k) + 1)).2))

/-- Add two complex rectangles coordinatewise at the same scale. Addition is exact in integer
ticks and combines the previous odd prefix with its next block. -/
def dyadicBoxAdd (A B : Analysis.IntegerInterval × Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  (A.1.add B.1, A.2.add B.2)

/-- Compute rectangles for the dyadic power sum and its odd prefix together. The input `Q`
encloses the base-two complex power, and `B` supplies odd-term rectangles. At each level the
new odd block is added once and one outward-rounded complex multiplication performs the Horner
step. The result is used by compact finite Euler–Maclaurin certificates. -/
def dyadicOddBoxPair (G : ℤ) (Q : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) :
    ℕ →
      (Analysis.IntegerInterval × Analysis.IntegerInterval) ×
        (Analysis.IntegerInterval × Analysis.IntegerInterval)
  | 0 => (B 1, B 1)
  | m + 1 =>
    let v := dyadicOddBoxPair G Q B m
    let odd := dyadicBoxAdd v.2 (dyadicOddBlockBox B m)
    (dyadicBoxAdd odd (Analysis.roundedComplexProduct G Q v.1), odd)

/-- At positive scale, certified base-two and odd-term rectangles enclose both components of the
dyadic power-sum pair. The assumptions request only term one and the finite odd blocks used up
to depth `m`. Induction composes finite-sum containment, addition, and computed multiplication;
the result supplies the main-sum enclosure for compact EM8 certificates. -/
theorem dyadicOddBoxPair_contains (G : ℤ) (Q : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (s : ℂ) (hG : 0 < G)
    (hQ : Analysis.complexIntervalContains Q.1 Q.2 G ((2 : ℂ) ^ (-s)))
    (h1 : Analysis.complexIntervalContains (B 1).1 (B 1).2 G (dyadicPowerTerm s 1)) (m : ℕ)
    (hB :
      ∀ j < m,
        ∀ k ∈ Finset.range (2 ^ j),
          Analysis.complexIntervalContains (B (2 * (2 ^ j + k) + 1)).1 (B (2 * (2 ^ j + k) + 1)).2 G
            (dyadicPowerTerm s (2 * (2 ^ j + k) + 1))) :
    Analysis.complexIntervalContains (dyadicOddBoxPair G Q B m).1.1 (dyadicOddBoxPair G Q B m).1.2 G
        (dyadicOddPair s m).1 ∧
      Analysis.complexIntervalContains (dyadicOddBoxPair G Q B m).2.1 (dyadicOddBoxPair G Q B m).2.2
        G (dyadicOddPair s m).2 := by
  induction m with
  | zero => exact ⟨h1, h1⟩
  | succ m ih =>
    have hp := ih (fun j hj ↦ hB j (Nat.lt_trans hj (Nat.lt_succ_self m)))
    have hblock :=
      Analysis.complex_sum_contains (Finset.range (2 ^ m)) (fun k ↦ (B (2 * (2 ^ m + k) + 1)).1)
        (fun k ↦ (B (2 * (2 ^ m + k) + 1)).2) (fun k ↦ dyadicPowerTerm s (2 * (2 ^ m + k) + 1)) G
        (fun k hk ↦ hB m (Nat.lt_succ_self m) k hk)
    have hodd := Analysis.complex_add_contains hp.2 hblock
    have hprod := Analysis.roundedComplexProduct_contains hG hQ hp.1
    have hsum := Analysis.complex_add_contains hodd hprod
    exact ⟨hsum, hodd⟩

/-- Compute the cutoff-512 Euler–Maclaurin rectangle from the base-two power rectangle `Q`,
the grouped correction coefficient rectangle `C`, and the odd-term rectangles `B`. The main
sum uses eight cumulative odd-prefix steps, while the cutoff power uses three squares and one
product. The output is consumed by a separate endpoint sign certificate. -/
def dyadicEM8Box (G : ℤ) (Q C : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  dyadicBoxAdd (dyadicOddBoxPair G Q B 8).1
    (Analysis.roundedComplexProduct G C (Analysis.roundedComplexPow9 G Q))

/-- Certified base-two, correction-coefficient, and odd-term rectangles enclose the complete
cutoff-512 Euler–Maclaurin finite expression. The proof combines the finite odd-sum invariant,
the ninth-power enclosure, the grouped correction, and the exact Euler–Maclaurin identity.
The assumptions concern only the finite odd blocks used by this checker; no zero existence or
sign of the expression is assumed. -/
theorem dyadicEM8Box_contains (G : ℤ) (Q C : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (t : ℝ) (hG : 0 < G)
    (hQ :
      Analysis.complexIntervalContains Q.1 Q.2 G
        ((2 : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))))
    (hC : Analysis.complexIntervalContains C.1 C.2 G (finiteEM8CoefficientAt 512 t))
    (h1 :
      Analysis.complexIntervalContains (B 1).1 (B 1).2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) 1))
    (hB :
      ∀ j < 8,
        ∀ k ∈ Finset.range (2 ^ j),
          Analysis.complexIntervalContains (B (2 * (2 ^ j + k) + 1)).1 (B (2 * (2 ^ j + k) + 1)).2 G
            (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) (2 * (2 ^ j + k) + 1))) :
    Analysis.complexIntervalContains (dyadicEM8Box G Q C B).1 (dyadicEM8Box G Q C B).2 G
      (finiteEM8At 512 t) := by
  have hmain := (dyadicOddBoxPair_contains G Q B _ hG hQ h1 8 hB).1
  have hpow := Analysis.roundedComplexPow9_contains hG hQ
  have hcorr := Analysis.roundedComplexProduct_contains hG hC hpow
  have hsum := Analysis.complex_add_contains hmain hcorr
  have hf := finiteEM8At_oddPair t 8
  norm_num only [show (2 : ℕ) ^ 9 = 512 by decide] at hf
  rw [hf]
  exact hsum

/-- A single certified family for odd bases 1 through 511 supplies every odd block needed by the
cutoff-512 Euler–Maclaurin enclosure. The index bounds follow from the dyadic block sizes.
This interface connects factor-family certificates to the computed finite expression. -/
theorem dyadicEM8Box_family (G : ℤ) (Q C : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (t : ℝ) (hG : 0 < G)
    (hQ :
      Analysis.complexIntervalContains Q.1 Q.2 G
        ((2 : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))))
    (hC : Analysis.complexIntervalContains C.1 C.2 G (finiteEM8CoefficientAt 512 t))
    (hfamily :
      ∀ n,
        Odd n →
          0 < n →
          n ≤ 511 →
          Analysis.complexIntervalContains (B n).1 (B n).2 G
            (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) n)) :
    Analysis.complexIntervalContains (dyadicEM8Box G Q C B).1 (dyadicEM8Box G Q C B).2 G
      (finiteEM8At 512 t) := by
  apply dyadicEM8Box_contains G Q C B t hG hQ hC
  · exact hfamily 1 ⟨0, by decide⟩ (by decide) (by decide)
  · intro j hj k hk
    have hk' : k < 2 ^ j := Finset.mem_range.mp hk
    have hp : 2 ^ j ≤ (2 : ℕ) ^ 7 := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ hj)
    norm_num only [show (2 : ℕ) ^ 7 = 128 by decide] at hp
    apply hfamily
    · exact ⟨2 ^ j + k, by simp only [two_mul]⟩
    · exact Nat.zero_lt_succ _
    · nlinarith only [hk', hp]

/-- Acyclic odd-factor certificates enclose the complete cutoff-512 finite EM8 expression.
Each odd term is either enclosed directly or computed from two smaller odd factors; the
factor-family induction supplies every odd block used by the finite-expression evaluator.
The base-two and correction rectangles remain separate inputs to the endpoint certificate. -/
theorem dyadicEM8Box_factored (G : ℤ) (Q C : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (t : ℝ) (hG : 0 < G)
    (hQ :
      Analysis.complexIntervalContains Q.1 Q.2 G
        ((2 : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))))
    (hC : Analysis.complexIntervalContains C.1 C.2 G (finiteEM8CoefficientAt 512 t))
    (hstep :
      ∀ n,
        Odd n →
          0 < n →
          n ≤ 511 →
          Analysis.complexIntervalContains (B n).1 (B n).2 G
              (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) n) ∨
            ∃ a b,
              Odd a ∧
                Odd b ∧
                0 < a ∧
                0 < b ∧
                a < n ∧ b < n ∧ a * b = n ∧ B n = Analysis.roundedComplexProduct G (B a) (B b)) :
    Analysis.complexIntervalContains (dyadicEM8Box G Q C B).1 (dyadicEM8Box G Q C B).2 G
      (finiteEM8At 512 t) := by
  exact dyadicEM8Box_family G Q C B t hG hQ hC (factoredFamily_contains G B _ 511 Odd hG hstep)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
