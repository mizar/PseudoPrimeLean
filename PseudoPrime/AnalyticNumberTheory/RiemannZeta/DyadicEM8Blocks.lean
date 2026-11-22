/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicEM8Intervals
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalTermSums

/-! # Euler–Maclaurin enclosures from certified odd blocks -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The rectangle sum of concatenated witness lists is the coordinatewise sum of the two
rectangle sums. List induction and associativity of integer addition let separately certified
literal block sums be reused in larger odd blocks. -/
theorem criticalTermSum_append (G e : ℤ) (xs ys : List CriticalTermWitness) :
    criticalTermSum G e (xs ++ ys) =
      dyadicBoxAdd (criticalTermSum G e xs) (criticalTermSum G e ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, criticalTermSum, dyadicBoxAdd, Analysis.IntegerInterval.add,
      Int.zero_add]
  | cons w ws ih =>
    simp only [List.cons_append, criticalTermSum, ih, dyadicBoxAdd, Analysis.IntegerInterval.add,
      Int.add_assoc]

/-- A traversed list of certified terms encloses an odd finite sum when its base list equals the
specified odd progression. The base equality is a decidable condition on natural numbers; the
proof changes the list sum into a finite sum without indexing any list element. -/
theorem criticalTermSum_oddRange (G e : ℤ) (s : ℂ) (data : List CriticalTermWitness) (a b : ℕ)
    (hb : data.map (fun w ↦ w.log.base) = (List.range b).map (fun k ↦ 2 * (a + k) + 1))
    (h :
      ∀ w ∈ data,
        Analysis.complexIntervalContains (w.result G e).1 (w.result G e).2 G
          (dyadicPowerTerm s w.log.base)) :
    Analysis.complexIntervalContains (criticalTermSum G e data).1 (criticalTermSum G e data).2 G
      (∑ k ∈ Finset.range b, dyadicPowerTerm s (2 * (a + k) + 1)) := by
  have hsum := criticalTermSum_contains G e s data h
  have hid :
    (data.map fun w ↦ dyadicPowerTerm s w.log.base).sum =
      ∑ k ∈ Finset.range b, dyadicPowerTerm s (2 * (a + k) + 1) := by
    have hmap := congrArg (List.map (dyadicPowerTerm s)) hb
    simp only [List.map_map, Function.comp_def] at hmap
    rw [hmap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  rw [hid] at hsum
  exact hsum

/-- Evaluate the cumulative odd-prefix and dyadic-sum recurrence from precomputed block
rectangles. `A` encloses the term at one, `Q` encloses the power at two, and `R m` encloses
the new odd block at depth `m`. Each step adds one block and performs one rounded product. -/
def oddBlockBoxPair (G : ℤ) (Q A : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (R : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) :
    ℕ →
      (Analysis.IntegerInterval × Analysis.IntegerInterval) ×
        (Analysis.IntegerInterval × Analysis.IntegerInterval)
  | 0 => (A, A)
  | m + 1 =>
    let v := oddBlockBoxPair G Q A R m
    let odd := dyadicBoxAdd v.2 (R m)
    (dyadicBoxAdd odd (Analysis.roundedComplexProduct G Q v.1), odd)

/-- If the power at two, the term at one, and each required odd block are enclosed, the
computed recurrence encloses both components of the mathematical dyadic pair. Induction adds
the newly certified block and multiplies the preceding sum by the shared base-two power. -/
theorem oddBlockBoxPair_contains (G : ℤ) (Q A : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (R : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (s : ℂ) (hG : 0 < G)
    (hQ : Analysis.complexIntervalContains Q.1 Q.2 G ((2 : ℂ) ^ (-s)))
    (h1 : Analysis.complexIntervalContains A.1 A.2 G (dyadicPowerTerm s 1)) (m : ℕ)
    (hR :
      ∀ j < m,
        Analysis.complexIntervalContains (R j).1 (R j).2 G
          (∑ k ∈ Finset.range (2 ^ j), dyadicPowerTerm s (2 * (2 ^ j + k) + 1))) :
    Analysis.complexIntervalContains (oddBlockBoxPair G Q A R m).1.1 (oddBlockBoxPair G Q A R m).1.2
        G (dyadicOddPair s m).1 ∧
      Analysis.complexIntervalContains (oddBlockBoxPair G Q A R m).2.1
        (oddBlockBoxPair G Q A R m).2.2 G (dyadicOddPair s m).2 := by
  induction m with
  | zero => exact ⟨h1, h1⟩
  | succ m ih =>
    have hp := ih (fun j hj ↦ hR j (Nat.lt_trans hj (Nat.lt_succ_self m)))
    have hodd := Analysis.complex_add_contains hp.2 (hR m (Nat.lt_succ_self m))
    have hprod := Analysis.roundedComplexProduct_contains hG hQ hp.1
    exact ⟨Analysis.complex_add_contains hodd hprod, hodd⟩

/-- Combine eight certified odd blocks and a grouped correction coefficient into a rectangle
for the cutoff-512 finite EM8 expression. The base-two power and term at one are shared. -/
def dyadicEM8BlocksBox (G : ℤ) (Q A C : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (R : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  dyadicBoxAdd (oddBlockBoxPair G Q A R 8).1
    (Analysis.roundedComplexProduct G C (Analysis.roundedComplexPow9 G Q))

/-- Certified odd-block sums, base-two power, term one, and grouped correction enclose the
complete finite EM8 expression at cutoff 512. The recurrence and the exact grouped identity
assemble the partial results without retrieving values from a list by index. -/
theorem dyadicEM8BlocksBox_contains (G : ℤ)
    (Q A C : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (R : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (t : ℝ) (hG : 0 < G)
    (hQ :
      Analysis.complexIntervalContains Q.1 Q.2 G
        ((2 : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))))
    (hA :
      Analysis.complexIntervalContains A.1 A.2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) 1))
    (hC : Analysis.complexIntervalContains C.1 C.2 G (finiteEM8CoefficientAt 512 t))
    (hR :
      ∀ j < 8,
        Analysis.complexIntervalContains (R j).1 (R j).2 G
          (∑ k ∈ Finset.range (2 ^ j),
            dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) (2 * (2 ^ j + k) + 1))) :
    Analysis.complexIntervalContains (dyadicEM8BlocksBox G Q A C R).1
      (dyadicEM8BlocksBox G Q A C R).2 G (finiteEM8At 512 t) := by
  have hmain := (oddBlockBoxPair_contains G Q A R _ hG hQ hA 8 hR).1
  have hpow := Analysis.roundedComplexPow9_contains hG hQ
  have hcorr := Analysis.roundedComplexProduct_contains hG hC hpow
  have hsum := Analysis.complex_add_contains hmain hcorr
  have hf := finiteEM8At_oddPair t 8
  norm_num only [show (2 : ℕ) ^ 9 = 512 by decide] at hf
  rw [hf]
  exact hsum

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
