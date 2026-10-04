/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Selfridge.Wheel30
import PseudoPrime.PrimeTest.JacobiFuel
import PseudoPrime.PrimeTest.Selfridge.MethodAStar
import PseudoPrime.PrimeTest.StrongLucas.Loop
import PseudoPrime.PrimeTest.StrongLucas.Fast
import PseudoPrime.PrimeTest.StrongLucas.NoGcd
import PseudoPrime.PrimeTest.Decision
import PseudoPrime.PrimeTest.BPSW.Exec
import Mathlib.Data.List.Find
import PseudoPrime.PrimeTest.Selfridge.Nonempty
import PseudoPrime.PrimeTest.Selfridge.WitnessBounds

/-! # Certified finite factor-detecting Selfridge scan

The ascending scan filters Wheel30 candidates and connects its stopping evidence
to ordinary and strengthened MR-first decision consumers without assuming GRH.
-/

namespace PseudoPrime.PrimeTest

/-- Test the factor-detecting Wheel30 stopping predicate.
Zero Jacobi values and minus-one values stop only when n does not divide the magnitude. -/
def selfridgeNeOneStop (n i : ℕ) : Bool :=
  wheel30NeOneCandidate i &&
    (decide (¬n ∣ i) && decide (ReferenceArithmetic.jacobiExecutable (selfridgeD i) n ≠ 1))

/-- The Boolean stopping test agrees with the mathematical stopping set.
Explicit Boolean rules connect the executable guards to the first-stop specification. -/
theorem selfridgeNeOneStop_iff (n i : ℕ) :
    selfridgeNeOneStop n i = true ↔ i ∈ FirstStopNeOneSet isWheel30NeOneCandidate n := by
  simp only [selfridgeNeOneStop, ReferenceArithmetic.jacobiExecutable_eq, Bool.and_eq_true,
    decide_eq_true_eq, wheel30NeOneCandidate_eq_true_iff, FirstStopNeOneSet, Set.mem_ofPred_eq]

/-- Scan increasing magnitudes without allocating a candidate list.
Fuel counts magnitudes, not Wheel30 candidates; skipped residues do not evaluate Jacobi.
The first stop returns its magnitude, while exhausted fuel returns none. -/
def selfridgeNeOneScan (n start : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    if selfridgeNeOneStop n start then some start else selfridgeNeOneScan n (start + 1) fuel

/-- The finite recursive scan equals an ascending list search.
The list is used only in this proof specification and is not built by execution. -/
theorem selfridgeNeOneScan_eq_find (n start fuel : ℕ) :
    selfridgeNeOneScan n start fuel = (List.range' start fuel).find? (selfridgeNeOneStop n) := by
  induction fuel generalizing start with
  | zero => simp only [selfridgeNeOneScan, List.range'_zero, List.find?_nil]
  | succ fuel ih =>
    rw [selfridgeNeOneScan, List.range'_succ, List.find?_cons]
    cases selfridgeNeOneStop n start <;> simp only [Bool.false_eq_true, ↓reduceIte, ih]

/-- Every returned magnitude belongs to the factor-detecting stopping set.
List search soundness supplies the candidate, divisibility, and Jacobi conditions. -/
theorem selfridgeNeOneScan_sound {n start fuel i : ℕ}
    (h : selfridgeNeOneScan n start fuel = some i) :
    i ∈ FirstStopNeOneSet isWheel30NeOneCandidate n := by
  rw [selfridgeNeOneScan_eq_find] at h
  exact (selfridgeNeOneStop_iff n i).mp (List.find?_some h)

/-- Exhaustion means no stopping candidate occurs in the scanned interval.
This contract does not turn an insufficient caller budget into non-primality. -/
theorem selfridgeNeOneScan_none {n start fuel : ℕ} :
    selfridgeNeOneScan n start fuel = none ↔
      ∀ i ∈ List.range' start fuel, i ∉ FirstStopNeOneSet isWheel30NeOneCandidate n := by
  rw [selfridgeNeOneScan_eq_find, List.find?_eq_none]
  simp only [selfridgeNeOneStop_iff]

/-- A zero Jacobi stop yields a proper factor of a positive input.
The excluded divisibility case prevents the gcd from being n; zero Jacobi prevents gcd one. -/
theorem selfridgeStop_gcd_bounds {n i : ℕ} (hn : 0 < n) (hdiv : ¬n ∣ i)
    (hzero : jacobiSym (selfridgeD i) n = 0) : 1 < Nat.gcd i n ∧ Nat.gcd i n < n := by
  have hne := (jacobiSym.eq_zero_iff.mp hzero).2
  rw [Int.gcd_eq_natAbs, selfridgeD_natAbs, Int.natAbs_natCast] at hne
  refine
    ⟨Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.ne_of_gt (Nat.gcd_pos_of_pos_right i hn), hne⟩, ?_⟩
  exact
    Nat.lt_of_le_of_ne (Nat.le_of_dvd hn (Nat.gcd_dvd_right i n))
      (fun h ↦ hdiv (Nat.gcd_eq_right_iff_dvd.mp h))

/-- A returned magnitude is the least stop at or above the starting value.
Induction preserves the lower bound and excludes every earlier magnitude. -/
theorem selfridgeNeOneScan_minimal {n start fuel i : ℕ}
    (h : selfridgeNeOneScan n start fuel = some i) :
    start ≤ i ∧ ∀ j, start ≤ j → j < i → selfridgeNeOneStop n j = false := by
  induction fuel generalizing start with
  | zero =>
    change (none : Option ℕ) = some i at h
    cases h
  | succ fuel ih =>
    by_cases hs : selfridgeNeOneStop n start = true
    · have hi : start = i := by
        simpa only [selfridgeNeOneScan, hs, ↓reduceIte, Option.some.injEq] using h
      subst i
      exact ⟨le_rfl, fun j hj hji ↦ False.elim ((Nat.not_lt_of_ge hj) hji)⟩
    · have ht : selfridgeNeOneScan n (start + 1) fuel = some i := by
        simpa only [selfridgeNeOneScan, Bool.eq_false_iff.mpr hs, Bool.false_eq_true,
          ↓reduceIte] using h
      obtain ⟨hle, hmin⟩ := ih ht
      refine ⟨Nat.le_trans (Nat.le_succ start) hle, fun j hj hji ↦ ?_⟩
      rcases Nat.eq_or_lt_of_le hj with heq | hlt
      · exact Bool.eq_false_iff.mpr (heq ▸ hs)
      · exact hmin j (Nat.succ_le_of_lt hlt) hji

/-- A stopping candidate within the finite interval guarantees a returned stop.
This consumes bounded witness evidence without assuming an analytic hypothesis. -/
theorem selfridgeNeOneScan_isSome {n start fuel : ℕ}
    (h : ∃ i ∈ List.range' start fuel, i ∈ FirstStopNeOneSet isWheel30NeOneCandidate n) :
    (selfridgeNeOneScan n start fuel).isSome = true := by
  rw [selfridgeNeOneScan_eq_find, List.find?_isSome]
  obtain ⟨i, hi, hs⟩ := h
  exact ⟨i, hi, (selfridgeNeOneStop_iff n i).mpr hs⟩

/-- A scan starting at five returns the mathematical Wheel30 first stop.
Scan minimality and the minimum specification provide both inequalities. -/
theorem selfridgeNeOneScan_firstStop {n fuel i : ℕ} (hs : selfridgeNeOneScan n 5 fuel = some i)
    (h : (FirstStopNeOneSet isWheel30NeOneCandidate n).Nonempty) :
    i = firstStopNeOne isWheel30NeOneCandidate n h := by
  have hm := firstStopNeOne_mem isWheel30NeOneCandidate n h
  have hlo := (wheel30NeOneCandidate_classical hm.1).1
  have hmin := (selfridgeNeOneScan_minimal hs).2
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hlt
    have hf := hmin _ hlo hlt
    exact Bool.false_ne_true (hf.symm.trans ((selfridgeNeOneStop_iff n _).mpr hm))
  · exact firstStopNeOne_le _ _ h (selfridgeNeOneScan_sound hs)

/-- A bound on the mathematical first stop gives sufficient finite scan fuel.
Candidate membership supplies the lower bound five. -/
theorem selfridgeNeOneScan_terminates {n fuel : ℕ}
    (h : (FirstStopNeOneSet isWheel30NeOneCandidate n).Nonempty)
    (hbound : firstStopNeOne isWheel30NeOneCandidate n h < 5 + fuel) :
    (selfridgeNeOneScan n 5 fuel).isSome = true := by
  have hm := firstStopNeOne_mem isWheel30NeOneCandidate n h
  apply selfridgeNeOneScan_isSome
  exact ⟨_, List.mem_range'_1.mpr ⟨(wheel30NeOneCandidate_classical hm.1).1, hbound⟩, hm⟩

/-- Find the next candidate offset by checking the next five Wheel30 predicates.
The fallback offset is six; from magnitude five onward it also reaches a candidate.
This bounded lookahead allocates no candidate list and evaluates no Jacobi symbols. -/
def wheel30Gap (i : ℕ) : ℕ :=
  if wheel30NeOneCandidate (i + 1) then 1
  else
    if wheel30NeOneCandidate (i + 2) then 2
    else
      if wheel30NeOneCandidate (i + 3) then 3
      else
        if wheel30NeOneCandidate (i + 4) then 4 else if wheel30NeOneCandidate (i + 5) then 5 else 6

/-- Every candidate jump is positive and at most six.
These bounds justify termination and the finite skipped-residue proof. -/
theorem wheel30Gap_bounds (i : ℕ) : 0 < wheel30Gap i ∧ wheel30Gap i ≤ 6 := by
  unfold wheel30Gap
  split_ifs <;> decide

/-- No magnitude strictly inside the jump is a Wheel30 candidate.
The bounded offsets reduce to the earlier failed candidate checks. -/
theorem wheel30Gap_skipped {i k : ℕ} (hkpos : 1 ≤ k) (hk : k < wheel30Gap i) :
    wheel30NeOneCandidate (i + k) = false := by
  have hk5 : k ≤ 5 := Nat.le_of_lt_succ (hk.trans_le (wheel30Gap_bounds i).2)
  interval_cases k
  all_goals
    unfold wheel30Gap at hk
    split_ifs at hk with h1 h2 h3 h4 h5 <;> norm_num only [Nat.reduceLT] at hk
  all_goals
    first
    | exact Bool.eq_false_iff.mpr h1
    | exact Bool.eq_false_iff.mpr h2
    | exact Bool.eq_false_iff.mpr h3
    | exact Bool.eq_false_iff.mpr h4
    | exact Bool.eq_false_iff.mpr h5

/-- Every strictly skipped magnitude fails the Selfridge stopping predicate.
The false Wheel30 guard prevents a Jacobi test at that magnitude. -/
theorem selfridgeNeOneStop_skipped {n i k : ℕ} (hkpos : 1 ≤ k) (hk : k < wheel30Gap i) :
    selfridgeNeOneStop n (i + k) = false := by
  simp only [selfridgeNeOneStop, wheel30Gap_skipped hkpos hk, Bool.false_and]

/-- A block containing no stops may be removed from the magnitude-by-magnitude scan.
The equation accounts for the full block length in the remaining magnitude budget. -/
theorem selfridgeNeOneScan_skip (n start gap fuel : ℕ)
    (h : ∀ k < gap, selfridgeNeOneStop n (start + k) = false) :
    selfridgeNeOneScan n start (gap + fuel) = selfridgeNeOneScan n (start + gap) fuel := by
  induction gap generalizing start with
  | zero => simp only [Nat.zero_add, Nat.add_zero]
  | succ gap
    ih =>
    have hzero : selfridgeNeOneStop n start = false := by
      simpa only [Nat.add_zero] using h 0 (Nat.zero_lt_succ gap)
    have htail : ∀ k < gap, selfridgeNeOneStop n (start + 1 + k) = false := by
      intro k hk
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h (k + 1) (Nat.succ_lt_succ hk)
    simp only [Nat.succ_add, selfridgeNeOneScan, hzero, Bool.false_eq_true, ↓reduceIte]
    rw [ih _ htail]
    rw [Nat.add_assoc, Nat.add_comm 1 gap]

/-- After a failed current stop, the whole block before the next candidate contains no stops.
The current value uses its failed test; positive offsets use the skipped-candidate theorem. -/
theorem selfridgeNeOneStop_gap {n start : ℕ} (h : selfridgeNeOneStop n start = false) :
    ∀ k < wheel30Gap start, selfridgeNeOneStop n (start + k) = false := by
  intro k hk
  cases k with
  | zero => simpa only [Nat.add_zero] using h
  | succ k => exact selfridgeNeOneStop_skipped (Nat.succ_le_succ (Nat.zero_le k)) hk

/-- Check the eight Wheel30 residue classes used above the initial candidate range.
This Boolean helper specifies the periodic tail for the next-candidate proof. -/
def wheel30Tail (r : ℕ) : Bool :=
  decide (r = 1) || decide (r = 7) || decide (r = 11) || decide (r = 13) || decide (r = 17) ||
    decide (r = 19) ||
    decide (r = 23) ||
    decide (r = 29)

/-- Above twenty-nine the executable candidate test depends only on the residue modulo thirty.
All exceptional initial equalities are excluded by the lower bound. -/
theorem wheel30NeOneCandidate_tail {i : ℕ} (hi : 29 < i) :
    wheel30NeOneCandidate i = wheel30Tail (i % 30) := by
  have hnot : ∀ a ≤ 29, i ≠ a := fun a ha ↦ Nat.ne_of_gt (ha.trans_lt hi)
  simp only [wheel30NeOneCandidate, hnot 5 (by decide), hnot 7 (by decide), hnot 9 (by decide),
    hnot 11 (by decide), hnot 13 (by decide), hnot 15 (by decide), hnot 17 (by decide),
    hnot 19 (by decide), hnot 23 (by decide), hnot 29 (by decide), decide_false, decide_true, hi,
    Bool.false_or, Bool.true_and]
  rfl

/-- From every magnitude at least five, the jump lands on the next Wheel30 candidate.
Initial values and the thirty tail residues are checked in the Lean kernel.
Together with wheel30Gap_skipped this fixes the complete candidate order. -/
theorem wheel30Gap_next {i : ℕ} (hi : 5 ≤ i) : wheel30NeOneCandidate (i + wheel30Gap i) = true := by
  by_cases hsmall : i ≤ 29
  · interval_cases i <;> decide +kernel
  · have hlarge : 29 < i := Nat.lt_of_not_ge hsmall
    have ht (j : ℕ) : wheel30NeOneCandidate (i + j) = wheel30Tail ((i + j) % 30) :=
      wheel30NeOneCandidate_tail (hlarge.trans_le (Nat.le_add_right i j))
    rw [ht]
    rw [Nat.add_mod]
    simp only [wheel30Gap, ht, Nat.add_mod i 1, Nat.add_mod i 2, Nat.add_mod i 3, Nat.add_mod i 4,
      Nat.add_mod i 5]
    have hmod : i % 30 < 30 := Nat.mod_lt i (by decide)
    interval_cases i % 30 <;> decide +kernel

/-- Generate the next gap using the initial candidate values and a modulo-thirty table.
Noncandidate small inputs use bounded lookahead so the function remains total.
The production path starts at five and visits only valid candidates. -/
def wheel30GapFast (i : ℕ) : ℕ :=
  if i ≤ 29 then
    match i with
    | 5 | 7 | 9 | 11 | 13 | 15 | 17 | 29 => 2
    | 19 => 4
    | 23 => 6
    | _ => wheel30Gap i
  else
    match i % 30 with
    | 0 | 6 | 10 | 12 | 16 | 18 | 22 | 28 => 1
    | 5 | 9 | 11 | 15 | 17 | 21 | 27 | 29 => 2
    | 4 | 8 | 14 | 20 | 26 => 3
    | 3 | 7 | 13 | 19 | 25 => 4
    | 2 | 24 => 5
    | 1 | 23 => 6
    | _ => 2

/-- The constant-table generator equals bounded lookahead for every magnitude.
Initial inputs and the thirty residue classes are verified by kernel reduction. -/
theorem wheel30GapFast_eq (i : ℕ) : wheel30GapFast i = wheel30Gap i := by
  by_cases hs : i ≤ 29
  · simp only [wheel30GapFast, hs, ↓reduceIte]
    interval_cases i <;> decide +kernel
  · have hl : 29 < i := Nat.lt_of_not_ge hs
    have ht (j : ℕ) : wheel30NeOneCandidate (i + j) = wheel30Tail ((i + j) % 30) :=
      wheel30NeOneCandidate_tail (hl.trans_le (Nat.le_add_right i j))
    simp only [wheel30GapFast, hs, ↓reduceIte, wheel30Gap, ht, Nat.add_mod i 1, Nat.add_mod i 2,
      Nat.add_mod i 3, Nat.add_mod i 4, Nat.add_mod i 5]
    have hm : i % 30 < 30 := Nat.mod_lt i (by decide)
    interval_cases i % 30 <;> decide +kernel

/-- Search with bounded candidate jumps and no candidate-list allocation.
Fuel keeps its existing meaning as a magnitude interval length.
If the next candidate lies outside that interval, return none; otherwise subtract the jump. -/
def selfridgeNeOneJump (n start fuel : ℕ) : Option ℕ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if selfridgeNeOneStop n start then some start
    else
      if fuel + 1 < wheel30GapFast start then none
      else selfridgeNeOneJump n (start + wheel30GapFast start) (fuel + 1 - wheel30GapFast start)
termination_by fuel
decreasing_by
  simp only [wheel30GapFast_eq]
  exact Nat.sub_lt (Nat.zero_lt_succ _) (wheel30Gap_bounds _).1

/-- The jumping scan equals the original scan for every input, start, and budget.
Strong induction applies the skipped-block equation.
Exhaustion is preserved at interval boundaries. -/
theorem selfridgeNeOneJump_eq (n start fuel : ℕ) :
    selfridgeNeOneJump n start fuel = selfridgeNeOneScan n start fuel := by
  induction fuel using Nat.strong_induction_on generalizing start with
  | h fuel ih =>
    cases fuel with
    | zero => rw [selfridgeNeOneJump, selfridgeNeOneScan]
    | succ fuel =>
      rw [selfridgeNeOneJump]
      simp only [wheel30GapFast_eq]
      by_cases hs : selfridgeNeOneStop n start = true
      · simp only [hs, ↓reduceIte, selfridgeNeOneScan]
      · have hf := Bool.eq_false_iff.mpr hs
        have hgap := selfridgeNeOneStop_gap hf
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        by_cases hb : fuel + 1 < wheel30Gap start
        · simp only [hb, ↓reduceIte]
          have hskip :=
            selfridgeNeOneScan_skip n start (fuel + 1) 0 (fun k hk ↦ hgap k (hk.trans hb))
          simpa only [Nat.add_zero, selfridgeNeOneScan] using hskip.symm
        · have hle : wheel30Gap start ≤ fuel + 1 := Nat.le_of_not_gt hb
          simp only [hb, ↓reduceIte]
          rw [ih _ (Nat.sub_lt (Nat.zero_lt_succ _) (wheel30Gap_bounds _).1)]
          have hskip :=
            selfridgeNeOneScan_skip n start (wheel30Gap start) (fuel + 1 - wheel30Gap start) hgap
          rw [Nat.add_comm, Nat.sub_add_cancel hle] at hskip
          exact hskip.symm

/-- Every magnitude returned by the jumping scan carries the existing stopping-set evidence.
All-input scan equality transports the proof into parameter and factor classification. -/
theorem selfridgeNeOneJump_sound {n start fuel i : ℕ}
    (h : selfridgeNeOneJump n start fuel = some i) :
    i ∈ FirstStopNeOneSet isWheel30NeOneCandidate n :=
  selfridgeNeOneScan_sound ((selfridgeNeOneJump_eq _ _ _).symm.trans h)

/-- Proof-carrying outcomes of finite Selfridge search.
Selected parameters carry Jacobi minus one; factors carry proper-divisor evidence.
Exhausted records an insufficient budget and supports only an unknown decision. -/
inductive SelfridgeScanResult (n : ℕ) where
  | exhausted
  | selected (param : LucasParams) (jacobi : jacobiSym param.D n = -1)
  | factor (g : ℕ) (lower : 1 < g) (upper : g < n) (dvd : g ∣ n)

/-- Classify a sound returned magnitude independently of its scan implementation.
The first-stop evidence supports Method A* selection or certified factor detection. -/
def selfridgeNeOneClassify (n : ℕ) (found : Option ℕ)
    (sound : ∀ i, found = some i → i ∈ FirstStopNeOneSet isWheel30NeOneCandidate n) :
    SelfridgeScanResult n :=
  if hn : 0 < n then
    match hs : found with
    | none => .exhausted
    | some i =>
      have hm := sound i rfl
      letI : Decidable (jacobiSym (selfridgeD i) n = -1) :=
        ReferenceArithmetic.jacobiEqDecidable (selfridgeD i) n (-1)
      if hj : jacobiSym (selfridgeD i) n = -1 then
        let param :=
          LucasParams.methodAStar (selfridgeD i)
            (selfridgeD_methodA_mod_four (wheel30NeOneCandidate_classical hm.1).2)
        have hd : param.D = selfridgeD i := by
          dsimp only [param, LucasParams.methodAStar]
          split <;> rfl
        .selected param (hd.symm ▸ hj)
      else
        have hz : jacobiSym (selfridgeD i) n = 0 :=
          (jacobiSym.trichotomy _ _).resolve_right (fun h ↦ h.elim hm.2.2 hj)
        let hg := selfridgeStop_gcd_bounds hn hm.2.1 hz
        .factor (Nat.gcd i n) hg.1 hg.2 (Nat.gcd_dvd_right i n)
  else .exhausted

/-- Equal sound scan results give identical certified classifications.
Proof irrelevance identifies the stopping-set and divisor evidence. -/
theorem selfridgeNeOneClassify_congr (n : ℕ) (a b : Option ℕ)
    (ha : ∀ i, a = some i → i ∈ FirstStopNeOneSet isWheel30NeOneCandidate n)
    (hb : ∀ i, b = some i → i ∈ FirstStopNeOneSet isWheel30NeOneCandidate n) (h : a = b) :
    selfridgeNeOneClassify n a ha = selfridgeNeOneClassify n b hb := by
  cases h
  rfl

/-- Classify the first finite stop as Method A* parameters or a proper factor.
Nonpositive input and exhaustion remain inconclusive.
The selected branch carries Jacobi evidence. -/
def selfridgeNeOneResult (n fuel : ℕ) : SelfridgeScanResult n :=
  selfridgeNeOneClassify n (selfridgeNeOneJump n 5 fuel) (fun _ h ↦ selfridgeNeOneJump_sound h)

/-- Consume a search outcome using the ordinary shared-initial-value Strong Lucas test.
Proper factors and failed prime-pass tests prove non-primality; acceptance remains unknown. -/
def SelfridgeScanResult.decide {n : ℕ} : SelfridgeScanResult n → Decision n
  | .exhausted => .unknown
  | .factor _ hl hu hd => .notPrime (Nat.not_prime_of_dvd_of_lt hd hl hu)
  | .selected param hj =>
    decideByPrimePass n (strongLucasWithParamsFast n param.D param.P param.Q)
      (fun hp ↦ strongLucasWithParamsFast_of_prime hp _ _ _ param.discr hj)

/-- Run finite factor-detecting Selfridge search and consume its ordinary Lucas outcome.
Caller fuel exhaustion returns unknown through the certified decision interface. -/
def selfridgeNeOneDecision (n fuel : ℕ) : Decision n :=
  (selfridgeNeOneResult n fuel).decide

/-- Every odd nonsquare has a stop within the unconditional budget of 2*n magnitudes.
Above fifteen use the classical first-stop bound and Wheel30 equality.
Small inputs are kernel checked. -/
theorem selfridgeNeOneScan_total {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) :
    (selfridgeNeOneScan n 5 (2 * n)).isSome = true := by
  by_cases hlarge : 15 < n
  · have hc := classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
    have hw := wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
    have hp :=
      primeNeOneWitnessSet_nonempty_of_negOne
        (primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
    have hb := classicalFirstStopNeOne_lt_of_odd_nonsquare_of_fifteen_lt hn hns hlarge hp hc
    apply selfridgeNeOneScan_terminates hw
    rw [firstStopNeOne_wheel30_eq_classical hn.pos hn hns hc hw]
    exact
      hb.trans_le ((Nat.le_mul_of_pos_left n (by decide : 0 < 2)).trans (Nat.le_add_left (2 * n) 5))
  · have hle : n ≤ 15 := Nat.le_of_not_gt hlarge
    interval_cases n <;> norm_num only [Nat.odd_iff, Nat.reduceMod] at hn
    all_goals
      first
      | exact False.elim (hns ⟨1, rfl⟩)
      | exact False.elim (hns ⟨3, rfl⟩)
      | decide +kernel

/-- Valid selected parameters pass the shared strengthened Lucas conditions at prime inputs.
The all-input shared equality transfers the existing Strong, V, and Euler prime-pass theorems. -/
theorem strengthenedLucasSharedEuler_of_prime {n : ℕ} (hp : n.Prime) (param : LucasParams)
    (hj : jacobiSym param.D n = -1) :
    strengthenedLucasSharedEuler n param.D param.P param.Q = true := by
  rw [strengthenedLucasSharedEuler_eq, Bool.and_eq_true, Bool.and_eq_true]
  exact
    ⟨strongLucasWithParams_of_prime hp _ _ _ param.discr hj,
      lucasVWithParams_of_prime hp _ _ _ param.discr hj, eulerJacobiWithIntBase_of_prime hp _⟩

/-- Valid selected parameters pass the gcd-free shared strengthened evaluator at primes.
The all-input equality preserves the certified prime-pass implication. -/
theorem strengthenedLucasSharedEulerValid_of_prime {n : ℕ} (hp : n.Prime) (param : LucasParams)
    (hj : jacobiSym param.D n = -1) : strengthenedLucasSharedEulerValid n param = true := by
  rw [strengthenedLucasSharedEulerValid_eq]
  exact strengthenedLucasSharedEuler_of_prime hp param hj

/-- Consume the selected parameters using the shared strengthened Lucas test.
Every rejection is certified; probable-prime acceptance and exhausted fuel stay unknown. -/
def SelfridgeScanResult.decideStrengthened {n : ℕ} : SelfridgeScanResult n → Decision n
  | .exhausted => .unknown
  | .factor _ hl hu hd => .notPrime (Nat.not_prime_of_dvd_of_lt hd hl hu)
  | .selected param hj =>
    decideByPrimePass n (strengthenedLucasSharedEulerValid n param)
      (fun hp ↦ strengthenedLucasSharedEulerValid_of_prime hp param hj)

/-- Run successive-square MR before square checking and finite factor-detecting search.
The strengthened flag selects the shared strengthened Lucas consumer.
Fuel exhaustion is unknown; the original public Boolean entries remain comparison interfaces. -/
def BPSW.decideWheel30Within (n fuel : ℕ) (strengthened : Bool := false) : Decision n :=
  if n < 3 then decideByTest bailliePSWMRFirst bailliePSWMRFirst_spec n
  else
    if ho : Odd n then
      if hm : strongMillerRabinWithBaseLoop n 2 = false then
        .notPrime
          (fun hp ↦
            Bool.noConfusion
              (hm.symm.trans
                ((strongMillerRabinWithBaseLoop_eq n 2).trans
                  (strongMillerRabinWithBase_of_prime hp (Nat.coprime_two_left.mpr ho)))))
      else
        if natIsSquare n then decideByTest bailliePSWMRFirst bailliePSWMRFirst_spec n
        else
          let result := selfridgeNeOneResult n fuel
          if strengthened then result.decideStrengthened else result.decide
    else decideByTest bailliePSWMRFirst bailliePSWMRFirst_spec n

/-- Report whether a search outcome carries parameters or a proper factor.
This observable separates completed search from caller-budget exhaustion. -/
def SelfridgeScanResult.hasStop {n : ℕ} : SelfridgeScanResult n → Bool
  | .exhausted => false
  | .selected _ _ => true
  | .factor _ _ _ _ => true

/-- For a positive modulus, classification preserves completion of every sound scan result.
Both selected parameters and proper factors count as completed outcomes. -/
theorem selfridgeNeOneClassify_hasStop {n : ℕ} (hn : 0 < n) (found : Option ℕ)
    (sound : ∀ i, found = some i → i ∈ FirstStopNeOneSet isWheel30NeOneCandidate n) :
    (selfridgeNeOneClassify n found sound).hasStop = found.isSome := by
  cases found with
  | none =>
    simp only [selfridgeNeOneClassify, hn, ↓reduceDIte, SelfridgeScanResult.hasStop,
      Option.isSome_none]
  | some i =>
    simp only [selfridgeNeOneClassify, hn, ↓reduceDIte]
    split <;> rfl

/-- For positive inputs, classification preserves the finite scan completion flag.
The selected and factor branches both represent the returned stopping magnitude. -/
theorem selfridgeNeOneResult_hasStop {n fuel : ℕ} (hn : 0 < n) :
    (selfridgeNeOneResult n fuel).hasStop = (selfridgeNeOneScan n 5 fuel).isSome := by
  rw [selfridgeNeOneResult, selfridgeNeOneClassify_hasStop hn, selfridgeNeOneJump_eq]

/-- Odd nonsquare inputs never exhaust the unconditional 2*n search budget.
The raw scan termination theorem removes the incomplete outcome at this consumer boundary. -/
theorem selfridgeNeOneResult_total {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) :
    (selfridgeNeOneResult n (2 * n)).hasStop = true := by
  rw [selfridgeNeOneResult_hasStop hn.pos]
  exact selfridgeNeOneScan_total hn hns

/-- The gcd-free finite-search decision preserves the guarded consumer on every outcome.
Factors remain certified rejections, exhaustion remains unknown, and selected results coincide. -/
theorem SelfridgeScanResult.decideStrengthened_eq_guarded {n : ℕ} (result : SelfridgeScanResult n) :
    result.decideStrengthened =
      (match result with
      | .exhausted => .unknown
      | .factor _ hl hu hd => .notPrime (Nat.not_prime_of_dvd_of_lt hd hl hu)
      | .selected param hj =>
        decideByPrimePass n (strengthenedLucasSharedEuler n param.D param.P param.Q)
          (fun hp ↦ strengthenedLucasSharedEuler_of_prime hp param hj)) := by
  cases result with
  | exhausted => rfl
  | factor g hl hu hd => rfl
  | selected param hj =>
    simp only [SelfridgeScanResult.decideStrengthened, strengthenedLucasSharedEulerValid_eq,
      decideByPrimePass]

end PseudoPrime.PrimeTest
