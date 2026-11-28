/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleCommonMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWideTransfer644

/-! # Common-sign translated triangle on section 122 radii -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH the two halves of the translated Mangoldt sum have total mass strictly above
3943r/400 for radii from 316 to 322. Use the certified logarithm bound at radius 322. -/
theorem triangle_mangoldt_lower_322 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    let v := 2 * Real.log r
    let l := Real.exp v
    let m := Real.exp (v + 5 / 2)
    let u := Real.exp (v + 5)
    let f := triangleLogBranch (-(2 * v / 5)) (2 / 5)
    let g := triangleLogBranch (2 + 2 * v / 5) (-(2 / 5))
    3943 / 400 * r <
      (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊m⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ Finset.Ioc ⌊m⌋₊ ⌊u⌋₊, g n * ArithmeticFunction.vonMangoldt n) := by
  apply triangle_mangoldt_lower_of_bound hRH (show 287 ≤ r by linarith only [hr.1])
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo := 5) (hi :=
        231 / 40) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hv := (Real.log_le_log (show 0 < r by linarith only [hr.1]) hr.2).trans h
  have hs := pow_le_pow_left₀ (Real.log_nonneg (show 1 ≤ r by linarith only [hr.1])) hv 2
  linarith only [hr.1, hv, hs]

/-- For radii from 316 to 322, the translated triangle bounds the mass
on common Jacobi signs below. -/
theorem triangle_common_mass_322 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 316 ≤ R)
    (hU : R ≤ 322) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    2343 / 1600 * R + 4197 / 1000 <
      ∑ b ∈ s.filter (fun (b : ℕ) ↦ jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r),
        w b := by
  intro v s w
  let S {k : ℕ} (χ : DirichletCharacter ℂ k) := ∑ b ∈ s, w b * (χ (b : ZMod k)).re
  let A := S (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq))
  let B := S (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr))
  let C := S (NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr))
  have hR' : 287 ≤ R := by linarith only [hR]
  have hf := triangle_triple_window hn ho hs he hp hq hr hk hj hm hv hw hGRH hR' hb
  dsimp only at hf
  simp_rw [triangle_signed_weight_sum] at hf
  change |A| + |B| + |C| < _ at hf
  rw [hL] at hf
  have hsum :=
    triangle_pair_indicator_sum hp hq hr s w
      (fun b ht ↦
        ⟨triangle_window_gcd_of_large hR' (Fact.out : p.Prime) hP ht,
          triangle_window_gcd_of_large hR' (Fact.out : q.Prime) hQ ht,
          triangle_window_gcd_of_large hR' (Fact.out : r.Prime) hT ht⟩)
  change 4 * _ = (∑ b ∈ s, w b) + A + B + C at hsum
  have hm := triangle_mangoldt_lower_322 hRH ⟨hR, hU⟩
  have hm0 : 3943 / 400 * R < ∑ b ∈ s, w b :=
    hm.trans_eq (triangle_branch_sum v (fun b ↦ ArithmeticFunction.vonMangoldt b)).symm
  linarith only [hsum, hm0, hf, neg_le_abs A, neg_le_abs B, neg_le_abs C]

/-- Removing composite prime powers leaves more than 73/50 times the
radius in common-sign primes throughout section 122. -/
theorem triangle_common_prime_mass_322 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 316 ≤ R)
    (hU : R ≤ 322) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let v := 2 * Real.log R
    let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
    let w (b : ℕ) :=
      shiftedTriangle (5 / 2) (Real.log b - v) / Real.sqrt b * ArithmeticFunction.vonMangoldt b
    73 / 50 * R <
      ∑
        b ∈
          s.filter
            (fun (b : ℕ) =>
              (jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) ∧ b.Prime),
        w b := by
  intro v s w
  let good :=
    s.filter (fun (b : ℕ) => jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r)
  have ha :=
    triangle_common_mass_322 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hRH hP hQ hT hb
  change _ < ∑ b ∈ good, w b at ha
  have hr0 : 0 < R := by linarith only [hR]
  have hx : Real.exp v = R ^ 2 := by
    dsimp only [v]; rw [two_mul, Real.exp_add, Real.exp_log hr0, sq]
  let bad := good.filter (fun b ↦ ¬b.Prime)
  have hmem {b : ℕ} (hh : b ∈ bad) : b ∈ s := (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  have hbad :=
    triangle_mangoldt_nonprime_322 ⟨hR, hU⟩ bad (fun b hh ↦ (Finset.mem_filter.mp hh).2)
      (fun b ↦ Real.log b - v)
      (fun b hh ↦ hx ▸ (Nat.floor_lt (Real.exp_pos _).le).mp (Finset.mem_Ioc.mp (hmem hh)).1)
      (fun b hh ↦ by
        rw [← hx, mul_comm, ← Real.exp_add]
        exact (Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Ioc.mp (hmem hh)).2)
  simp_rw [mul_comm (ArithmeticFunction.vonMangoldt _) _] at hbad
  change (∑ b ∈ bad, w b) < 5.1 at hbad
  have ht := Finset.sum_filter_add_sum_filter_not good Nat.Prime w
  have heq :=
    Finset.filter_filter (s := s) (p := fun (b : ℕ) =>
      jacobiSym b p = jacobiSym b q ∧ jacobiSym b q = jacobiSym b r) (q := Nat.Prime)
  rw [← heq]
  change _ < ∑ b ∈ good.filter Nat.Prime, w b
  change _ + (∑ b ∈ bad, w b) = _ at ht
  linarith only [ha, hbad, ht, hR]

/-- For the three primitive even pair characters of a uniform triple,
agreement up to the squared radius and the translated triangle yield the
section 122 zero-mass bound with the wide Euler credit included. -/
theorem triangle_pair_mass_upper_644 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : R ∈ Set.Icc 316 322)
    (hL : Real.log n = 2 * R) (hP : R ^ 4 < p) (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hpass :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → c l = 1) →
      quarterMass644 a + quarterMass644 b + quarterMass644 c ≤
        3 / 4 * R - 11.7421197 + 4 * positiveTail644 (R ^ 2) - 0.0113 := by
  intro a b c hA hB hC
  have hpq : p * q ∣ n := ⟨r, he⟩
  have hpr : p * r ∣ n := ⟨q, he.trans (by ac_rfl)⟩
  have hqr : q * r ∣ n := ⟨p, he.trans (by ac_rfl)⟩
  have level_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : 2 ≤ p * q :=
    hp.two_le.trans (Nat.le_mul_of_pos_right p hq.pos)
  have ha := level_two (Fact.out : p.Prime) (Fact.out : q.Prime)
  have hb := level_two (Fact.out : p.Prime) (Fact.out : r.Prime)
  have hc := level_two (Fact.out : q.Prime) (Fact.out : r.Prime)
  have ht : ∀ j : ℕ, -1 ≤ (a j).re + (b j).re + (c j).re := by
    intro j
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (j : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hlog : Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ) ≤ 4 * R := by
    rw [pair_level_log_sum he, hL]
    linarith only
  let v := 2 * Real.log R
  let S := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
  let T :=
    S.filter (fun l : ℕ ↦ (jacobiSym l p = jacobiSym l q ∧ jacobiSym l q = jacobiSym l r) ∧ l.Prime)
  have hR₀ : 0 < R := by linarith only [hR.1]
  have hx : Real.exp v = R ^ 2 := by
    dsimp only [v]
    rw [two_mul, Real.exp_add, Real.exp_log hR₀, sq]
  have hR' : 287 ≤ R := by linarith only [hR.1]
  have hT' :
    ∀ l ∈ T,
      l.Prime ∧
        R ^ 2 < l ∧ (a l).re + (b l).re + (c l).re = 3 ∧ Real.log l - 2 * Real.log R ≤ 5 := by
    intro l hl
    obtain ⟨hlS, hsign, hprime⟩ := Finset.mem_filter.mp hl
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hlS
    have h :=
      triangle_pair_indicator (l : ℤ) hp hq hr
        (triangle_window_gcd_of_large hR' (Fact.out : p.Prime) hP hlS)
        (triangle_window_gcd_of_large hR' (Fact.out : q.Prime) hQ hlS)
        (triangle_window_gcd_of_large hR' (Fact.out : r.Prime) hT hlS)
    simp only [Int.cast_natCast] at h
    rw [ite_eq_left hsign] at h
    have hh :=
      (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hprime.pos)).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp hhi)
    exact
      ⟨hprime, hx ▸ (Nat.floor_lt (Real.exp_pos _).le).mp hlo, by
        dsimp only [a, b, c]; linarith only [h], by linarith only [hh]⟩
  have hM :=
    triangle_common_prime_mass_322 hn ho hs he hp hq hr hk hj hm hv hw hG hR.1 hR.2 hL hG.riemann hP
      hQ hT hpass
  apply
    quarter_wide_mass_upper_644 ha hb hc hG
      ⟨pair_character_primitive hs hpq _, pair_character_ne_one hs hpq _ (Nat.lt_of_succ_le ha),
        pair_character_even_of_korselt hn ho hp hq hk hj hv⟩
      ⟨pair_character_primitive hs hpr _, pair_character_ne_one hs hpr _ (Nat.lt_of_succ_le hb),
        pair_character_even_of_korselt hn ho hp hr hk hm hw⟩
      ⟨pair_character_primitive hs hqr _, pair_character_ne_one hs hqr _ (Nat.lt_of_succ_le hc),
        pair_character_even_of_korselt hn ho hq hr hj hm (hw.trans hv.symm)⟩
      hR hlog ht hA hB hC T hT'
  apply hM.le.trans_eq
  apply Finset.sum_congr rfl
  intro l hl
  dsimp only
  rw [ArithmeticFunction.vonMangoldt_apply_prime (hT' l hl).1, mul_comm]

end PseudoPrime.PrimeTestBounds.MillerRabin
