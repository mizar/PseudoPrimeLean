/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass626
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterComparison632
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseEndpoints117
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformWideWindow
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness628

/-! # Quarter-square witness for logarithms above 628 through 632 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The three section 117 rows make the mass, phase and signed zero estimates
incompatible above radius 314 and through radius 316. -/
private theorem zero_bounds_contradict_632 {r M Z : ℝ} (hr : r ∈ Set.Ioc 314 316)
    (hM : M ≤ 3 / 4 * r - 13.4154 + 4 * positiveTail570 (r ^ 2) - 0.02085)
    (hP : 0.00120516 * r + threeShiftRemainder117 r ≤ M + Z)
    (hZ :
      0.717289 * r + quarterArithmeticTerm632 r + 0.1448 * 1.53 * ((r - 313) / 316) +
          (3 * (0.035 * (1 - (r - 313) / 313)) +
            (if r ≤ 6289 / 20 then 0.01980648 else 0.01963648)) +
          Z <
        section99Conductor r) :
    False := by
  have hr' : r ∈ Set.Icc 314 316 := ⟨hr.1.le, hr.2⟩
  have he := quarter_euler_envelope_632 hr'
  have hp := section117_remainder_lower hr'
  have ha : ¬r ≤ 1568 / 5 := by linarith only [hr.1]
  have hb : ¬r ≤ 314 := not_le.mpr hr.1
  unfold quarterArithmeticTerm632 at hZ
  rw [ite_eq_right ha, ite_eq_right hb] at hZ
  by_cases hc : r ≤ 6289 / 20
  · rw [ite_eq_left hc, ite_eq_left hc] at hZ
    rw [ite_eq_left hc] at he hp
    linarith only [hM, hP, hZ, he, hp, hc]
  rw [ite_eq_right hc, ite_eq_right hc] at hZ
  rw [ite_eq_right hc] at he hp
  by_cases hd : r ≤ 315
  · rw [ite_eq_left hd] at he hp hZ
    linarith only [hM, hP, hZ, he, hp, hd]
  rw [ite_eq_right hd] at he hp hZ
  linarith only [hM, hP, hZ, he, hp, hr.2]

/-- The three pair characters rule out universal passage up to the quarter-log-square
cutoff for a squarefree Korselt product with equal two-adic valuations. -/
theorem pair_impossible_632 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r] [Fact p.Prime]
    [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hsq : Squarefree n)
    (hnprod : n = p * q * r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n)
    (hrn : r ∣ n) (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hl : 628 < Real.log n)
    (hh : Real.log n ≤ 632) (hP : (Real.log n / 2) ^ 4 < p) (hQ : (Real.log n / 2) ^ 4 < q)
    (hT : (Real.log n / 2) ^ 4 < r)
    (hpass :
      ∀ l : ℕ,
        l.Prime → (l : ℝ) ≤ (Real.log n / 2) ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    False := by
  let X := (Real.log n / 2) ^ 2
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hpq : 2 ≤ p * q :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hpr : 2 ≤ p * r :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : r.Prime).pos)
  have hqr : 2 ≤ q * r :=
    (Fact.out : q.Prime).two_le.trans (Nat.le_mul_of_pos_right q (Fact.out : r.Prime).pos)
  have ha : a ≠ 1 := pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 2).trans_le hpq)
  have hb : b ≠ 1 := pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 2).trans_le hpr)
  have hc : c ≠ 1 := pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 2).trans_le hqr)
  have ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re := by
    intro k
    simpa only [Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1 := by
    intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hq hpn hqn hpqn hpK hqK hvq l (hpass l hl hlX)
  have hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1 := by
    intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hr hpn hrn hprn hpK hrK hvr l (hpass l hl hlX)
  have hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1 := by
    intro l hl hlX
    exact
      pair_character_nat_eq_one hn ho hq hr hqn hrn hqrn hqK hrK (hvr.trans hvq.symm) l
        (hpass l hl hlX)
  let R := Real.log n / 2
  have hR : 314 < R := by
    dsimp only [R]; linarith only [hl]
  have hU : R ≤ 316 := by
    dsimp only [R]; linarith only [hh]
  have hL : Real.log n = 2 * R := by
    dsimp only [R]; ring
  have hlev : Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ) ≤ 4 * R := by
    rw [pair_level_log_sum hnprod, hL]
    linarith only
  have ea := pair_character_even_of_korselt hn ho hp hq hpK hqK hvq
  have eb := pair_character_even_of_korselt hn ho hp hr hpK hrK hvr
  have ec := pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)
  have hZ :=
    signed_zero_upper_radius_632 hGRH a b c hpq hpr hqr
      (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc ea eb ec ⟨by linarith only [hR], hU⟩
      hlev ht hA hB hC
  have hM :=
    common_triple_mass_upper_to632 hn ho hsq hnprod hp hq hr hpK hqK hrK hvq hvr hGRH
      (show 300 ≤ R by linarith only [hR]) (show R ≤ 316 by linarith only [hU]) hL hP hQ hT hpass
  have hphase :=
    three_shift_passing_phase_117 hsq hn ho hp hq hr hpqn hprn hqrn hpK hqK hrK hvq hvr hGRH
      (show 300 ≤ R by linarith only [hR]) hL hnprod hpass
  dsimp only [twoShiftZeroPhase] at hphase
  apply
    zero_bounds_contradict_632 (M := quarterMass570 a + quarterMass570 b + quarterMass570 c)
      ⟨hR, hU⟩ _ _ hZ
  · linarith only [hM]
  · linarith only [hphase]

/-- Under GRH every odd uniform Korselt triple with logarithm above 628 and at most 632
has a prime strong Miller-Rabin witness at most the square of half its logarithm. -/
private theorem uniform_witness_above_628 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hl : 628 < Real.log n) (hh : Real.log n ≤ 632) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (Real.log n / 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hall :
    ∀ l : ℕ,
      l.Prime →
        (l : ℝ) ≤ (Real.log n / 2) ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    intro l hl' hlX
    exact Classical.byContradiction (fun hf ↦ h ⟨l, hl', hlX, hf⟩)
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hnprod⟩ := uniformKorselt_ordered_factors hu
  have hpD : p ∣ n := ⟨q * r, hnprod.trans (Nat.mul_assoc _ _ _)⟩
  have hqD : q ∣ n := ⟨p * r, hnprod.trans (by ac_rfl)⟩
  have hrD : r ∣ n := ⟨p * q, hnprod.trans (by ac_rfl)⟩
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have hpqD : p * q ∣ n := ⟨r, hnprod⟩
  have hprD : p * r ∣ n := ⟨q, hnprod.trans (by ac_rfl)⟩
  have hqrD : q * r ∣ n := ⟨p, hnprod.trans (by ac_rfl)⟩
  have hLarge := uniform_wideWindow_lt_prime hnprod hp hq hr hpq hqr hu (by linarith only [hl])
  have hQ := hLarge.trans (Nat.cast_lt.mpr hpq)
  have hT := hQ.trans (Nat.cast_lt.mpr hqr)
  exact
    pair_impossible_632 hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hl hh hLarge hQ hT hall

/-- Under GRH, an odd uniform Korselt triple with log n in [628,632]
has a prime strong Miller–Rabin witness at most the square of half its logarithm. -/
theorem uniform_witness_632 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hl : 628 ≤ Real.log n)
    (hh : Real.log n ≤ 632) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (Real.log n / 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  rcases lt_or_eq_of_le hl with h | h
  · exact uniform_witness_above_628 hn ho hu hGRH h hh
  · exact uniform_witness_628 hn ho hu hGRH (by linarith only [h]) h.ge

end PseudoPrime.PrimeTestBounds.MillerRabin
