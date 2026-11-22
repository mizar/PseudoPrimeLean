/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalExp
import Mathlib.Tactic.Ring

/-! # Complex exponential error for phase interval certificates -/

public section

namespace PseudoPrime.Analysis

/-- At complex norm at most one quarter, the 25-term exponential Taylor
polynomial has error at most `2^-120`. This controls both coordinates of a phase. -/
theorem complex_taylor24_error {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖Complex.exp z - ∑ m ∈ Finset.range 25, z ^ m / (m.factorial : ℂ)‖ ≤ (1 / 2 ^ 120 : ℝ) := by
  have hs : ‖z‖ / (25 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only at *
    linarith only [hz]
  have h := Complex.exp_bound' (n := 25) hs
  have hp := pow_le_pow_left₀ (norm_nonneg z) hz 25
  have hm := mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ 2 / (25 : ℕ).factorial by norm_num only)
  have hn : (1 / 4 : ℝ) ^ 25 * (2 / (25 : ℕ).factorial) ≤ 1 / 2 ^ 120 := by
    norm_num only [Nat.factorial]
  calc
    _ ≤ ‖z‖ ^ 25 / (25 : ℕ).factorial * 2 := h
    _ = ‖z‖ ^ 25 * (2 / (25 : ℕ).factorial) := by ring
    _ ≤ _ := hm.trans hn

/-- A complex error bound widens independent real and imaginary intervals.
Coordinate projection is bounded by the complex norm, providing the phase bridge. -/
theorem complex_error_contains {I J : IntegerInterval} {G r : ℤ} {z w : ℂ} (hr : I.Contains G w.re)
    (hi : J.Contains G w.im) (he : ‖z - w‖ ≤ (r : ℝ) / G) :
    (I.widen r).Contains G z.re ∧ (J.widen r).Contains G z.im := by
  constructor
  · exact IntegerInterval.widen_contains hr ((Complex.abs_re_le_norm (z - w)).trans he)
  · exact IntegerInterval.widen_contains hi ((Complex.abs_im_le_norm (z - w)).trans he)

/-- Rectangular complex containment using independent integer intervals for
real and imaginary coordinates at a common scale. Used by phase certificates. -/
@[expose]
def complexIntervalContains (R I : IntegerInterval) (G : ℤ) (z : ℂ) : Prop :=
  R.Contains G z.re ∧ I.Contains G z.im

/-- Three checked real products certify a complex square. The output coordinates
are `rr-ii` and `ri+ri`, so no further rounding is required for their sums. -/
theorem complex_square_contains {R I RR II RI : IntegerInterval} {G : ℤ} {z : ℂ}
    (hz : complexIntervalContains R I G z)
    (hrr : integerProductCheck G R.lower R.upper R.lower R.upper RR.lower RR.upper = true)
    (hii : integerProductCheck G I.lower I.upper I.lower I.upper II.lower II.upper = true)
    (hri : integerProductCheck G R.lower R.upper I.lower I.upper RI.lower RI.upper = true) :
    complexIntervalContains (RR.add II.neg) (RI.add RI) G (z * z) := by
  have hr := IntegerInterval.product_contains hrr hz.1 hz.1
  have hi := IntegerInterval.product_contains hii hz.2 hz.2
  have hm := IntegerInterval.product_contains hri hz.1 hz.2
  constructor
  · simpa only [Complex.mul_re, sub_eq_add_neg] using
      IntegerInterval.add_contains hr (IntegerInterval.neg_contains hi)
  · simpa only [Complex.mul_im, mul_comm] using IntegerInterval.add_contains hm hm

/-- Checked complex squaring doubles the certified phase angle. This connects
rectangular arithmetic to the range-reduced exponential phase computation. -/
theorem phase_double_contains {R I RR II RI : IntegerInterval} {G : ℤ} {x : ℝ}
    (hz : complexIntervalContains R I G (Complex.exp ((x : ℂ) * Complex.I)))
    (hrr : integerProductCheck G R.lower R.upper R.lower R.upper RR.lower RR.upper = true)
    (hii : integerProductCheck G I.lower I.upper I.lower I.upper II.lower II.upper = true)
    (hri : integerProductCheck G R.lower R.upper I.lower I.upper RI.lower RI.upper = true) :
    complexIntervalContains (RR.add II.neg) (RI.add RI) G
      (Complex.exp (((x + x : ℝ) : ℂ) * Complex.I)) := by
  have h := complex_square_contains hz hrr hii hri
  simpa only [← Complex.exp_add, Complex.ofReal_add, add_mul] using h

/-- Three product witnesses for a complex squaring step. `rr`, `ii`, and `ri`
enclose real-square, imaginary-square, and mixed products respectively. Their
integer checks, rather than construction, certify the step. -/
structure PhaseSquareWitness where
  rr : IntegerInterval
  ii : IntegerInterval
  ri : IntegerInterval

/-- Real output interval of a complex squaring witness, computed by subtraction. -/
@[expose]
def PhaseSquareWitness.realOut (w : PhaseSquareWitness) : IntegerInterval :=
  w.rr.add w.ii.neg

/-- Imaginary output interval of a complex squaring witness, computed by doubling. -/
@[expose]
def PhaseSquareWitness.imagOut (w : PhaseSquareWitness) : IntegerInterval :=
  w.ri.add w.ri

/-- Check every product in successive complex squarings, traversing witnesses
recursively and propagating each step's computed coordinate intervals. -/
@[expose]
def phaseSquareCheck (G : ℤ) (R I : IntegerInterval) : List PhaseSquareWitness → Bool
  | [] => true
  | w :: rest =>
    integerProductCheck G R.lower R.upper R.lower R.upper w.rr.lower w.rr.upper &&
      integerProductCheck G I.lower I.upper I.lower I.upper w.ii.lower w.ii.upper &&
      integerProductCheck G R.lower R.upper I.lower I.upper w.ri.lower w.ri.upper &&
      phaseSquareCheck G w.realOut w.imagOut rest

/-- Return the final coordinate intervals of a phase squaring certificate.
The initial pair is returned when the witness list is empty. -/
@[expose]
def phaseSquareResult (R I : IntegerInterval) :
    List PhaseSquareWitness → IntegerInterval × IntegerInterval
  | [] => (R, I)
  | w :: rest => phaseSquareResult w.realOut w.imagOut rest

/-- Successful checked squaring chains double the phase once per witness.
Induction composes the one-step phase theorem without indexed access to tables. -/
theorem phaseSquareCheck_sound (chain : List PhaseSquareWitness) (G : ℤ) (R I : IntegerInterval)
    (x : ℝ) (h : phaseSquareCheck G R I chain = true)
    (hx : complexIntervalContains R I G (Complex.exp ((x : ℂ) * Complex.I))) :
    complexIntervalContains (phaseSquareResult R I chain).1 (phaseSquareResult R I chain).2 G
      (Complex.exp ((((2 : ℝ) ^ chain.length * x : ℝ) : ℂ) * Complex.I)) := by
  induction chain generalizing R I x with
  | nil => simpa only [phaseSquareResult, List.length_nil, pow_zero, one_mul] using hx
  | cons w rest ih =>
    have hc := Bool.and_eq_true_iff.mp h
    have hp := Bool.and_eq_true_iff.mp hc.1
    have hq := Bool.and_eq_true_iff.mp hp.1
    have hw := phase_double_contains hx hq.1 hq.2 hp.2
    have hr := ih w.realOut w.imagOut (x + x) hc.2 hw
    have he : (2 : ℝ) ^ rest.length * (x + x) = 2 ^ (rest.length + 1) * x := by
      rw [pow_succ]
      ring
    simpa only [phaseSquareResult, List.length_cons, he] using hr

/-- Coordinate enclosures for a small-angle Taylor polynomial give certified
phase enclosures after widening by the analytic remainder. -/
theorem phase_taylor24_contains {R I : IntegerInterval} {G r : ℤ} {x : ℝ} (hx : |x| ≤ 1 / 4)
    (hp :
      complexIntervalContains R I G
        (∑ m ∈ Finset.range 25, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)))
    (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G) :
    complexIntervalContains (R.widen r) (I.widen r) G (Complex.exp ((x : ℂ) * Complex.I)) := by
  have hn : ‖(x : ℂ) * Complex.I‖ ≤ 1 / 4 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using hx
  exact complex_error_contains hp.1 hp.2 ((complex_taylor24_error hn).trans hr)

/-- A small-angle Taylor enclosure followed by a checked squaring chain
certifies the full phase `exp(i*x)`. This is the endpoint phase certificate interface. -/
theorem phase_reduced_contains (chain : List PhaseSquareWitness) (n : ℕ) (R I : IntegerInterval)
    (G r : ℤ) (x : ℝ) (hlen : chain.length = n) (hx : |x / (2 : ℝ) ^ n| ≤ 1 / 4)
    (hp :
      complexIntervalContains R I G
        (∑ m ∈ Finset.range 25, (((x / (2 : ℝ) ^ n : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)))
    (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G)
    (hc : phaseSquareCheck G (R.widen r) (I.widen r) chain = true) :
    complexIntervalContains (phaseSquareResult (R.widen r) (I.widen r) chain).1
      (phaseSquareResult (R.widen r) (I.widen r) chain).2 G
      (Complex.exp ((x : ℂ) * Complex.I)) := by
  have hi := phase_taylor24_contains hx hp hr
  have hs := phaseSquareCheck_sound chain G (R.widen r) (I.widen r) (x / (2 : ℝ) ^ n) hc hi
  rw [hlen] at hs
  have he : (2 : ℝ) ^ n * (x / (2 : ℝ) ^ n) = x := by
    exact mul_div_cancel₀ x (pow_ne_zero n (by norm_num only : (2 : ℝ) ≠ 0))
  rwa [he] at hs

/-- A certified central phase enclosure extends to nearby real phases by the
unit-exponential Lipschitz bound. This absorbs logarithm enclosure errors at endpoints. -/
theorem phase_perturb_contains {R I : IntegerInterval} {G r : ℤ} {x c : ℝ}
    (hc : complexIntervalContains R I G (Complex.exp ((c : ℂ) * Complex.I)))
    (hx : |x - c| ≤ (r : ℝ) / G) :
    complexIntervalContains (R.widen r) (I.widen r) G (Complex.exp ((x : ℂ) * Complex.I)) := by
  have h := norm_phase_exp_sub_le x c
  have he :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((c : ℂ) * Complex.I)‖ ≤ (r : ℝ) / G := by
    simpa only [mul_comm] using h.trans hx
  exact complex_error_contains hc.1 hc.2 he

/-- Four checked real products certify a general complex product. The output
coordinates are `ac-bd` and `ad+bc`, supporting phase rotation of finite EM8 sums. -/
theorem complex_mul_contains {A B C D AC BD AD BC : IntegerInterval} {G : ℤ} {z w : ℂ}
    (hz : complexIntervalContains A B G z) (hw : complexIntervalContains C D G w)
    (hac : integerProductCheck G A.lower A.upper C.lower C.upper AC.lower AC.upper = true)
    (hbd : integerProductCheck G B.lower B.upper D.lower D.upper BD.lower BD.upper = true)
    (had : integerProductCheck G A.lower A.upper D.lower D.upper AD.lower AD.upper = true)
    (hbc : integerProductCheck G B.lower B.upper C.lower C.upper BC.lower BC.upper = true) :
    complexIntervalContains (AC.add BD.neg) (AD.add BC) G (z * w) := by
  have ac := IntegerInterval.product_contains hac hz.1 hw.1
  have bd := IntegerInterval.product_contains hbd hz.2 hw.2
  have ad := IntegerInterval.product_contains had hz.1 hw.2
  have bc := IntegerInterval.product_contains hbc hz.2 hw.1
  constructor
  · simpa only [Complex.mul_re, sub_eq_add_neg] using
      IntegerInterval.add_contains ac (IntegerInterval.neg_contains bd)
  · simpa only [Complex.mul_im] using IntegerInterval.add_contains ad bc

/-- Coordinate interval addition certifies complex addition. This composes
finite Dirichlet terms without rounding the coordinate sums. -/
theorem complex_add_contains {A B C D : IntegerInterval} {G : ℤ} {z w : ℂ}
    (hz : complexIntervalContains A B G z) (hw : complexIntervalContains C D G w) :
    complexIntervalContains (A.add C) (B.add D) G (z + w) := by
  exact ⟨IntegerInterval.add_contains hz.1 hw.1, IntegerInterval.add_contains hz.2 hw.2⟩

/-- Sum integer interval endpoints over a finite set, at a common scale.
The result is used for Dirichlet sums without indexed list retrieval. -/
@[expose]
def intervalFinsetSum {ι : Type*} (S : Finset ι) (f : ι → IntegerInterval) : IntegerInterval :=
  ⟨∑ i ∈ S, (f i).lower, ∑ i ∈ S, (f i).upper⟩

/-- Termwise real interval containment composes into finite-sum containment.
Cast endpoint sums and distribute division before applying monotonicity of sums. -/
theorem intervalFinsetSum_contains {ι : Type*} (S : Finset ι) (f : ι → IntegerInterval) (v : ι → ℝ)
    (G : ℤ) (h : ∀ i ∈ S, (f i).Contains G (v i)) :
    (intervalFinsetSum S f).Contains G (∑ i ∈ S, v i) := by
  constructor
  · change ((∑ i ∈ S, (f i).lower : ℤ) : ℝ) / G ≤ ∑ i ∈ S, v i
    rw [Int.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum (fun i hi ↦ (h i hi).1)
  · change (∑ i ∈ S, v i) ≤ ((∑ i ∈ S, (f i).upper : ℤ) : ℝ) / G
    rw [Int.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum (fun i hi ↦ (h i hi).2)

/-- Coordinate certificates for every term enclose a finite complex sum.
Real and imaginary projections commute with finite sums, giving both bounds. -/
theorem complex_sum_contains {ι : Type*} (S : Finset ι) (R I : ι → IntegerInterval) (v : ι → ℂ)
    (G : ℤ) (h : ∀ i ∈ S, complexIntervalContains (R i) (I i) G (v i)) :
    complexIntervalContains (intervalFinsetSum S R) (intervalFinsetSum S I) G (∑ i ∈ S, v i) := by
  constructor
  · simpa only [Complex.re_sum] using
      intervalFinsetSum_contains S R (fun i ↦ (v i).re) G (fun i hi ↦ (h i hi).1)
  · simpa only [Complex.im_sum] using
      intervalFinsetSum_contains S I (fun i ↦ (v i).im) G (fun i hi ↦ (h i hi).2)

end PseudoPrime.Analysis
