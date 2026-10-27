/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionTheta
public import PseudoPrime.AnalyticNumberTheory.AGP.ExceptionalModuli
public import PseudoPrime.NumberTheory.PrimeProducts

/-! # Initial seed primes from fixed-scale theta bounds

Finite-divisor prime extraction for the primorial initial scale.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a primorial cutoff `z` and its full divisor range.

Claim: the restricted divisors of the primorial through `z` are exactly its
squarefree divisor set, whose cardinality is `2 ^ Nat.primeCounting z`.

Proof: use the primorial's prime-factor description, the squarefree divisor
count formula, and the fact that every divisor is at most the primorial.

Role: supplies the full-divisor source bound for the primorial seed construction.
-/
theorem restrictedDivisors_primorial_card_eq_primeCounting (z : ℕ) :
    let N := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id
    (restrictedDivisors N N).card = 2 ^ Nat.primeCounting z := by
  let N := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id
  change (restrictedDivisors N N).card = 2 ^ Nat.primeCounting z
  have hNpos : 0 < N := PseudoPrime.NumberTheory.PrimeProducts.primeProductLE_pos z
  have hdata := PseudoPrime.NumberTheory.PrimeProducts.primeProductLE_data z
  rw [restrictedDivisors_eq_divisors_of_le (Nat.ne_of_gt hNpos) (Nat.le_refl N)]
  rw [card_divisors_eq_two_pow_primeFactors_card (Nat.ne_of_gt hNpos) hdata.1, hdata.2,
    PseudoPrime.NumberTheory.PrimeProducts.primeSetLE_card]

/--
Inputs: a primorial cutoff `z` and a bound strictly below its prime count.

Claim: subtracting that bound from the prime count gives a positive exponent
whose exceptional-loss source `2 ^ (D + n)` is no larger than the full
restricted-divisor count of the primorial.

Proof: use `D + (primeCounting z - D) = primeCounting z` and the exact
primorial divisor count.

Role: provides the source-count hypotheses for the finite seed average.
-/
theorem primorial_seed_source_count_of_prime_count_lower (z D : ℕ) (hD : D < Nat.primeCounting z) :
    let n := Nat.primeCounting z - D
    0 < n ∧
      2 ^ (D + n) ≤
        (restrictedDivisors ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id)
            ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id)).card := by
  let n := Nat.primeCounting z - D
  change
    0 < n ∧
      2 ^ (D + n) ≤
        (restrictedDivisors ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id)
            ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id)).card
  constructor
  · exact Nat.sub_pos_of_lt hD
  · have hadd : D + n = Nat.primeCounting z := by
      dsimp only [n]
      exact Nat.add_sub_of_le (Nat.le_of_lt hD)
    rw [hadd, restrictedDivisors_primorial_card_eq_primeCounting]

/--
Inputs: a primorial cutoff, an exceptional-set budget below its prime count,
and the strict seed-average margin at the primorial scale.

Claim: the primorial supplies both the exceptional-loss source count and the
non-strict threshold bound needed by the seed construction.

Proof: set `n = primeCounting z - D`, apply the exact source-count lemma, and
rewrite the P2 margin using the modulus-one totient.

Role: turns the P2 scale's initial strict count estimate into the seed
constructor's finite-average hypotheses.
-/
theorem primorial_seed_initial_count_data_of_margin (z D q T : ℕ) (c₀ : ℝ)
    (hD : D < Nat.primeCounting z)
    (hmargin : (T : ℝ) < reliableProp15Coefficient c₀ 1 q * ((2 ^ Nat.primeCounting z : ℕ) : ℝ)) :
    ∃ n : ℕ,
      0 < n ∧
        2 ^ (D + n) ≤
          (restrictedDivisors ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id)
              ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id)).card ∧
        (T : ℝ) ≤ c₀ * ((2 ^ (D + n) : ℕ) : ℝ) / Real.log (q : ℝ) := by
  let n := Nat.primeCounting z - D
  have hsource := primorial_seed_source_count_of_prime_count_lower z D hD
  refine ⟨n, ?_, ?_, ?_⟩
  · exact hsource.1
  · exact hsource.2
  · have hadd : D + n = Nat.primeCounting z := by
      dsimp only [n]
      exact Nat.add_sub_of_le (Nat.le_of_lt hD)
    have hmargin' : (T : ℝ) ≤ (c₀ / Real.log (q : ℝ)) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
      simpa only [reliableProp15Coefficient, Nat.totient_one, Nat.cast_one, one_mul] using
        hmargin.le
    calc
      (T : ℝ) ≤ (c₀ / Real.log (q : ℝ)) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := hmargin'
      _ = c₀ * ((2 ^ (D + n) : ℕ) : ℝ) / Real.log (q : ℝ) := by
        rw [hadd]
        ring

/--
Inputs: a nonzero squarefree modulus, at most `D` exceptional moduli, and a
source lower bound for its full divisor count.

Claim: after removing exceptional factors and excluding the divisor `1`, the
remaining divisor count plus one is at least `2^n` whenever the source count is
at least `2^(D+n)`.

Proof: apply the established `2^D` exceptional divisor-loss bound, cancel the
factor `2^D`, and note that only the divisor `1` is lost by the final filter.

Role: tracks the exact finite loss needed for the primorial seed average.
-/
theorem exceptional_free_nontrivial_divisor_card_lower_of_source_count (L : ℕ) (E : Finset ℕ)
    (D n : ℕ) (hL : 0 < L) (hSquarefree : Squarefree L) (hEcard : E.card ≤ D)
    (hsource : 2 ^ (D + n) ≤ (restrictedDivisors L L).card) :
    2 ^ n ≤
      ((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter (fun d ↦ 1 < d)).card +
        1 := by
  let L' := exceptionalFreePartForModulus L E 1
  let R := restrictedDivisors L' L
  let D' := R.filter (fun d ↦ 1 < d)
  have hLprops := exceptionalFreePartForModulus_properties L E 1 (Nat.ne_of_gt hL) hSquarefree
  have hLdiv : L' ∣ L := hLprops.2.2.1
  have hL'ne : L' ≠ 0 := by
    intro hzero
    have hzeroDvd : 0 ∣ L := by simpa only [L', hzero] using hLdiv
    exact Nat.ne_of_gt hL (Nat.zero_dvd.mp hzeroDvd)
  have hloss :=
    restrictedDivisors_card_le_exceptional_modulus_count_bound L E 1 L D (Nat.ne_of_gt hL)
      hSquarefree hEcard
  have hkeep : 2 ^ n ≤ R.card := by
    have hmul : 2 ^ D * 2 ^ n ≤ 2 ^ D * R.card := by
      calc
        2 ^ D * 2 ^ n = 2 ^ (D + n) := by rw [← pow_add]
        _ ≤ (restrictedDivisors L L).card := hsource
        _ ≤ 2 ^ D * R.card := by simpa only [L', R] using hloss
    exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by norm_num only))
  have hsmall : ({d ∈ R | ¬1 < d}).card ≤ 1 := by
    have hsubset : {d ∈ R | ¬1 < d} ⊆ {1} := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hdR := (mem_restrictedDivisors hL'ne).mp hd'.1
      have hdpos : 0 < d := by
        by_contra hn
        have hz : d = 0 := Nat.eq_zero_of_not_pos hn
        subst d
        exact hL'ne (Nat.zero_dvd.mp hdR.1)
      have hdle : d ≤ 1 := Nat.not_lt.mp hd'.2
      have h1d : 1 ≤ d := Nat.succ_le_iff.mpr hdpos
      exact Finset.mem_singleton.mpr (Nat.le_antisymm hdle h1d)
    have hcard := Finset.card_le_card hsubset
    simpa only [Finset.card_singleton] using hcard
  have hpartition := Finset.card_filter_add_card_filter_not (s := R) (fun d : ℕ ↦ 1 < d)
  have hcardle : R.card ≤ D'.card + 1 := by
    calc
      R.card = D'.card + ({d ∈ R | ¬1 < d}).card := hpartition.symm
      _ ≤ D'.card + 1 := Nat.add_le_add_left hsmall D'.card
  simpa only [D'] using le_trans hkeep hcardle

/--
Inputs: the exceptional-modulus count bound, a source divisor count, and a
P2-derived threshold bound for the full source count.

Claim: after removing exceptional factors and omitting divisor `1`, the P2
threshold is at most the surviving divisor count divided by `64 log X^5`.

Proof: the divisor-loss lemma retains at least `2^n - 1` divisors. For `n ≥ 1`
this is at least half of `2^n`; the coefficient condition absorbs the loss
factor `2^D` and gives the required threshold.

Role: derives the finite-average input from primorial count data instead of
assuming that input separately for every exceptional set.
-/
theorem primorial_seed_threshold_bound_of_exceptional_loss (L : ℕ) (E : Finset ℕ) (D₀ n T : ℕ)
    (c₀ logX : ℝ) (hL : 0 < L) (hSquarefree : Squarefree L) (hEcard : E.card ≤ D₀) (hn : 0 < n)
    (hsource : 2 ^ (D₀ + n) ≤ (restrictedDivisors L L).card) (hfactor : c₀ * (2 : ℝ) ^ D₀ ≤ 1 / 128)
    (hlogX : 0 < logX) (hT : (T : ℝ) ≤ c₀ * ((2 ^ (D₀ + n) : ℕ) : ℝ) / logX) :
    (T : ℝ) ≤
      (((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter (fun d ↦ 1 < d)).card :
          ℝ) /
        (64 * logX) := by
  have hCard :=
    exceptional_free_nontrivial_divisor_card_lower_of_source_count L E D₀ n hL hSquarefree hEcard
      hsource
  have hpow : 2 ≤ 2 ^ n := Nat.le_self_pow (Nat.ne_of_gt hn) 2
  have hDpos :
    0 <
      ((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter
          (fun d ↦ 1 < d)).card := by
    omega
  have hcountNat :
    2 ^ n ≤
      2 *
        ((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter
            (fun d ↦ 1 < d)).card := by
    omega
  have hcountReal :
    (2 ^ n : ℝ) ≤
      2 *
        (((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter
              (fun d ↦ 1 < d)).card :
          ℝ) := by
    exact_mod_cast hcountNat
  have hpowCast : ((2 ^ (D₀ + n) : ℕ) : ℝ) = (2 : ℝ) ^ D₀ * (2 : ℝ) ^ n := by
    norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul, pow_add]
  have hfactorCount :
    (c₀ * (2 : ℝ) ^ D₀) * (2 : ℝ) ^ n ≤
      (1 / 128 : ℝ) *
        (2 *
          ((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter
              (fun d ↦ 1 < d)).card) := by
    exact
      mul_le_mul hfactor hcountReal (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) n)
        (by norm_num only)
  have hscaled :
    c₀ * ((2 ^ (D₀ + n) : ℕ) : ℝ) ≤
      (((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter (fun d ↦ 1 < d)).card :
          ℝ) /
        64 := by
    calc
      c₀ * ((2 ^ (D₀ + n) : ℕ) : ℝ) = (c₀ * (2 : ℝ) ^ D₀) * (2 : ℝ) ^ n := by
        rw [hpowCast]
        ring
      _ ≤
          (1 / 128 : ℝ) *
            (2 *
              ((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter
                  (fun d ↦ 1 < d)).card) :=
        hfactorCount
      _ =
          (((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter
                  (fun d ↦ 1 < d)).card :
              ℝ) /
            64 :=
        by ring
  calc
    (T : ℝ) ≤ c₀ * ((2 ^ (D₀ + n) : ℕ) : ℝ) / logX := hT
    _ ≤
        (((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter
                (fun d ↦ 1 < d)).card :
            ℝ) /
          64 /
          logX :=
      div_le_div_of_nonneg_right hscaled (le_of_lt hlogX)
    _ =
        (((restrictedDivisors (exceptionalFreePartForModulus L E 1) L).filter
                (fun d ↦ 1 < d)).card :
            ℝ) /
          (64 * logX) :=
      by ring

/--
Inputs: a finite set of positive divisors, their prime cutoffs, a common prime
bound, a parameter cutoff, theta lower bounds, and a strict average threshold.

Claim: one positive parameter produces more than `T` distinct primes below the
common bound, each of the form `d * k + 1` for some `d ∈ D`.

Proof: specialize the established theta and finite-average prime-set theorem to
modulus `1` and auxiliary modulus `1`; there are no bad quotient primes.

Role: supplies the primorial seed-prime interface without assuming the
all-input `ReliableProp15UniformCount` property.
-/
theorem exists_primorial_seed_prime_set_from_theta (D : Finset ℕ) (x : ℕ → ℕ) (xmax Kmax T : ℕ)
    (c : ℝ) (hxmax : 2 ≤ xmax) (hpos : ∀ d ∈ D, 0 < d) (hcut : ∀ d ∈ D, x d ≤ d * Kmax + 1)
    (hcommon : ∀ d ∈ D, x d ≤ xmax) (hx : ∀ d ∈ D, 2 ≤ x d)
    (hmodulus : ∀ d ∈ D, (18000000 * d) ^ 2 ≤ x d)
    (htheta :
      ∀ d,
        ∀ _hdD : d ∈ D,
          (x d : ℝ) / (2 * (Nat.totient d : ℝ)) ≤
            thetaInProgressionReal (x d : ℝ) (d * 1)
              (progressionCoprimeResidue d 1 1 (Nat.coprime_one_right d)))
    (htarget :
      ∀ d,
        ∀ _hdD : d ∈ D,
          c ≤
            agpFifthPowerAverageCoefficientOfProgressionBound 0 0 *
              ((x d : ℝ) / (Nat.totient (d * 1) : ℝ) / Real.log (xmax : ℝ)))
    (hlower : ((positiveCoprimeParameters 1 Kmax).card * T : ℕ) < c * (D.card : ℝ)) :
    ∃ k ∈ positiveCoprimeParameters 1 Kmax,
      ∃ P : Finset ℕ,
        T < P.card ∧ ∀ p ∈ P, Nat.Prime p ∧ p ≤ xmax ∧ p % 1 = 0 ∧ ∃ d ∈ D, p = d * k + 1 := by
  have hL : 1 ≠ 0 := by norm_num only
  have hLcoprime : Nat.Coprime 1 1 := by norm_num only
  have hrecip : (∑ q ∈ (1 : ℕ).primeFactors, (q : ℝ)⁻¹) ≤ (0 : ℝ) := by
    simp only [Nat.primeFactors_one, Finset.sum_empty]
    norm_num only
  have hBT :
    ∀ d,
      ∀ hdD : d ∈ D,
        ∀ q : { q // q ∈ (1 : ℕ).primeFactors },
          (primeCountInProgression (x d) (d * q.val * 1)
                (progressionCoprimeResidue (d * q.val) 1 1 (Nat.coprime_one_right (d * q.val))) :
              ℝ) ≤
            (0 : ℝ) * (q.val : ℝ)⁻¹ *
              ((x d : ℝ) / (Nat.totient (d * 1) : ℝ) / Real.log (xmax : ℝ)) := by
    intro d hdD q
    have hqempty : q.val ∈ (∅ : Finset ℕ) := by simpa only [Nat.primeFactors_one] using q.property
    exact False.elim (Finset.notMem_empty q.val hqempty)
  exact
    exists_prime_set_from_theta_lower_and_brun_titchmarsh_bounds D x xmax Kmax 1 1 1 T c 0 0
      (by norm_num only) hxmax (by norm_num only) hpos (fun _ _ => Nat.coprime_one_right _)
      (by norm_num only) hcut hcommon hx hL hLcoprime
      (by
        intro d hdD
        exact_mod_cast (by simpa only [Nat.mul_one] using hmodulus d hdD))
      (by
        intro d hdD
        simpa only [Nat.mul_one] using htheta d hdD)
      hrecip hBT
      (by
        intro d hdD
        simpa only [zero_mul, sub_zero, Nat.mul_one] using htarget d hdD)
      hlower

/--
Inputs: a squarefree primorial `N`, an exponent `J`, and the proposed
small-modulus theta estimate with a common exceptional set for each scale.

Claim: whenever `N^J ≤ X`, one exceptional set works for all nontrivial
divisors of its exceptional-free part, giving the theta lower bound in the
progression `1 mod d`.

Proof: each such divisor satisfies `d^J ≤ N^J ≤ X`. Remove the exceptional
factors at modulus `1`, use their avoidance property, and specialize the theta
estimate to modulus and residue `1`.

Role: feeds the primorial finite-average seed construction from the
small-modulus theta theorem required by the unconditional AGP proof.
-/
theorem primorial_seed_theta_bounds_of_small_modulus_supply (N J D₀ X₀ : ℕ) (hN : 0 < N)
    (hSquarefree : Squarefree N) (_hJ : 2 ≤ J)
    (hSupply :
      ∀ X : ℕ,
        X₀ ≤ X →
          ∃ E : Finset ℕ,
            E.card ≤ D₀ ∧
              (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
              ∀ m d a : ℕ,
                (m = 1 ∨ m = 4) →
                  0 < d →
                  Nat.Coprime d m →
                  1 < d * m →
                  (d * m) ^ J ≤ X →
                  Nat.Coprime a (d * m) →
                  (∀ e ∈ E, ¬e ∣ d * m) →
                  (((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                    thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * m) a) :
    ∀ X : ℕ,
      X₀ ≤ X →
        N ^ J ≤ X →
        ∃ E : Finset ℕ,
          E.card ≤ D₀ ∧
            (∀
              d ∈
                (restrictedDivisors (exceptionalFreePartForModulus N E 1) N).filter (fun d ↦ 1 < d),
              (((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient d : ℝ))) ≤
                thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) d
                  (progressionCoprimeResidue d 1 1 (Nat.coprime_one_right d))) := by
  intro X hXlarge hNX
  obtain ⟨E, hEcard, hEprops, htheta⟩ := hSupply X hXlarge
  have hEone : ∀ e ∈ E, 1 < e := fun e he ↦ (hEprops e he).1
  have hEm : ∀ e ∈ E, ¬e ∣ 1 := by
    intro e he heone
    apply (hEprops e he).2
    exact dvd_trans heone (by norm_num only : 1 ∣ 4)
  let L' := exceptionalFreePartForModulus N E 1
  have hLprops := exceptionalFreePartForModulus_properties N E 1 (Nat.ne_of_gt hN) hSquarefree
  have hLdiv : L' ∣ N := hLprops.2.2.1
  have hLne : L' ≠ 0 := by
    intro hzero
    have hzeroDvd : 0 ∣ N := by simpa only [L', hzero] using hLdiv
    exact Nat.ne_of_gt hN (Nat.zero_dvd.mp hzeroDvd)
  have hAvoid :=
    exceptionalFreePartForModulus_divisors_avoid N E 1 (Nat.ne_of_gt hN) hSquarefree hEone hEm
      (Nat.coprime_one_right N)
  refine ⟨E, hEcard, ?_⟩
  intro d hd
  have hd' := Finset.mem_filter.mp hd
  have hdDiv := (mem_restrictedDivisors hLne).mp hd'.1
  have hdN : d ≤ N := Nat.le_of_dvd hN (dvd_trans hdDiv.1 hLdiv)
  have hdJ : d ^ J ≤ N ^ J := Nat.pow_le_pow_left hdN J
  have hdX : d ^ J ≤ X := le_trans hdJ hNX
  have hAvoidD := hAvoid d hdDiv.1
  have hres := progressionCoprimeResidue_spec d 1 1 (Nat.coprime_one_right d) (by norm_num only)
  have hthetaD :=
    htheta 1 d (progressionCoprimeResidue d 1 1 (Nat.coprime_one_right d)) (Or.inl rfl)
      (Nat.lt_trans Nat.zero_lt_one hd'.2) (Nat.coprime_one_right d)
      (by simpa only [Nat.mul_one] using hd'.2) (by simpa only [Nat.mul_one] using hdX) hres.2.2
      hAvoidD
  simpa only [Nat.mul_one] using hthetaD

/--
Inputs: a prime-bound parameter `X ≥ 2` and a positive divisor `d`.

Claim: the coefficient `X^3 / (4 log(X^5))` is below the progression-count
target supplied by the raw fifth-power average coefficient at modulus `d`.

Proof: the totient is at most `d`, while the raw coefficient is greater than
`1/4`; divide this comparison by the positive logarithm.

Role: provides the common per-divisor target for the primorial finite-average
construction.
-/
theorem agp_primorial_seed_average_target (X d : ℕ) (hX : 2 ≤ X) (hd : 0 < d) :
    ((X : ℝ) ^ 3) / (4 * Real.log ((X ^ 5 : ℕ) : ℝ)) ≤
      agpFifthPowerAverageCoefficientOfProgressionBound 0 0 *
        (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 1) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hXpow : (32 : ℝ) ≤ ((X ^ 5 : ℕ) : ℝ) := by exact_mod_cast Nat.pow_le_pow_left hX 5
  have hX5 : (1 : ℝ) < ((X ^ 5 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num only) hXpow
  have hlog : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) := Real.log_pos hX5
  have hphiPos : 0 < (Nat.totient (d * 1) : ℝ) := by
    exact_mod_cast (by simpa only [Nat.mul_one] using (Nat.totient_pos.mpr hd))
  have hphiLe : (Nat.totient (d * 1) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (by simpa only [Nat.mul_one] using Nat.totient_le d)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdiv : (1 : ℝ) ≤ (d : ℝ) / (Nat.totient (d * 1) : ℝ) :=
    (le_div_iff₀ hphiPos).2 (by simpa only [one_mul] using hphiLe)
  have hmain : ((X : ℝ) ^ 3) ≤ ((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 1) : ℝ) := by
    calc
      (X : ℝ) ^ 3 = 1 * (X : ℝ) ^ 3 := by ring
      _ ≤ ((d : ℝ) / (Nat.totient (d * 1) : ℝ)) * (X : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hdiv (pow_nonneg (Nat.cast_nonneg X) 3)
      _ = ((d : ℝ) * (X : ℝ) ^ 3) / (Nat.totient (d * 1) : ℝ) := by ring
      _ = ((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 1) : ℝ) := by rw [Nat.cast_mul, Nat.cast_pow]
  have hcoeff : (1 / 4 : ℝ) ≤ agpFifthPowerAverageCoefficientOfProgressionBound 0 0 := by
    norm_num only [agpFifthPowerAverageCoefficientOfProgressionBound,
      agpFifthPowerRawPrimeCountCoefficient]
  have hcoeffNonneg : 0 ≤ agpFifthPowerAverageCoefficientOfProgressionBound 0 0 :=
    le_trans (by norm_num only) hcoeff
  have hscaled :
    ((X : ℝ) ^ 3) / 4 ≤
      agpFifthPowerAverageCoefficientOfProgressionBound 0 0 *
        (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 1) : ℝ)) := by
    calc
      ((X : ℝ) ^ 3) / 4 = (1 / 4 : ℝ) * (X : ℝ) ^ 3 := by ring
      _ ≤ agpFifthPowerAverageCoefficientOfProgressionBound 0 0 * (X : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (Nat.cast_nonneg X) 3)
      _ ≤
          agpFifthPowerAverageCoefficientOfProgressionBound 0 0 *
            (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left hmain hcoeffNonneg
  calc
    ((X : ℝ) ^ 3) / (4 * Real.log ((X ^ 5 : ℕ) : ℝ)) =
        (((X : ℝ) ^ 3) / 4) / Real.log ((X ^ 5 : ℕ) : ℝ) :=
      by ring
    _ ≤
        (agpFifthPowerAverageCoefficientOfProgressionBound 0 0 *
            (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 1) : ℝ))) /
          Real.log ((X ^ 5 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hscaled (le_of_lt hlog)
    _ =
        agpFifthPowerAverageCoefficientOfProgressionBound 0 0 *
          (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 1) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)) :=
      by ring

/--
Inputs: a positive logarithm, a nonempty divisor set, and a seed threshold
bound by `D.card / (64 log(X^5))`.

Claim: the finite-average lower bound is strict after multiplying by the
positive parameter count, whose size is at most `X^3`.

Proof: bound the admissible parameter count by `X^3`; the threshold margin
`1 / 64` then leaves room below the target coefficient `1 / 4`.

Role: converts the primorial source-count margin into the exact lower bound
required by `exists_primorial_seed_prime_set_from_theta`.
-/
theorem primorial_seed_average_lower_of_divisor_count (X T : ℕ) (D : Finset ℕ) (hX : 2 ≤ X)
    (hDpos : 0 < D.card) (hlog : 0 < Real.log ((X ^ 5 : ℕ) : ℝ))
    (hThreshold : (T : ℝ) ≤ (D.card : ℝ) / (64 * Real.log ((X ^ 5 : ℕ) : ℝ))) :
    (((positiveCoprimeParameters 1 (X ^ 3)).card * T : ℕ) : ℝ) <
      ((X : ℝ) ^ 3 / (4 * Real.log ((X ^ 5 : ℕ) : ℝ))) * (D.card : ℝ) := by
  have hParamCard : (positiveCoprimeParameters 1 (X ^ 3)).card ≤ X ^ 3 := by
    rw [positiveCoprimeParameters]
    calc
      ((Finset.Icc 1 (X ^ 3)).filter (fun k ↦ Nat.Coprime k 1)).card ≤
          (Finset.Icc 1 (X ^ 3)).card :=
        Finset.card_filter_le _ _
      _ = X ^ 3 + 1 - 1 := Nat.card_Icc 1 (X ^ 3)
      _ = X ^ 3 := by omega
  have hTbound : (T : ℝ) ≤ (D.card : ℝ) / (64 * Real.log ((X ^ 5 : ℕ) : ℝ)) := by exact hThreshold
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hXDpos : 0 < (X : ℝ) ^ 3 * (D.card : ℝ) :=
    mul_pos (pow_pos hXpos 3) (by exact_mod_cast hDpos)
  have hratio : (1 / 64 : ℝ) < 1 / 4 := by norm_num only
  have hstrict := mul_lt_mul_of_pos_right hratio hXDpos
  calc
    (((positiveCoprimeParameters 1 (X ^ 3)).card * T : ℕ) : ℝ) ≤ (X : ℝ) ^ 3 * T := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hParamCard) (Nat.cast_nonneg T)
    _ ≤ (X : ℝ) ^ 3 * ((D.card : ℝ) / (64 * Real.log ((X ^ 5 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hTbound (pow_nonneg (Nat.cast_nonneg X) 3)
    _ < (((1 / 4 : ℝ) * ((X : ℝ) ^ 3 * (D.card : ℝ))) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
      calc
        _ = (((1 / 64 : ℝ) * ((X : ℝ) ^ 3 * (D.card : ℝ))) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by ring
        _ < (((1 / 4 : ℝ) * ((X : ℝ) ^ 3 * (D.card : ℝ))) / Real.log ((X ^ 5 : ℕ) : ℝ)) :=
          div_lt_div_of_pos_right hstrict hlog
    _ = ((X : ℝ) ^ 3 / (4 * Real.log ((X ^ 5 : ℕ) : ℝ))) * (D.card : ℝ) := by ring

/--
Inputs: a squarefree primorial candidate `N`, a small-modulus theta supply, a
large fifth-power scale `X`, and the divisor-average lower bound.

Claim: one fixed parameter `k` gives more than `T` distinct primes `d*k+1`
from the nontrivial divisors of the exceptional-free part of `N`, all below
`X^5`.

Proof: use the small-modulus supply on each divisor, derive the per-divisor
average target from the theta bound, verify the fifth-power scale conditions,
and apply the existing finite-average prime-set theorem.

Role: constructs the initial primorial seed prime set needed before selecting
the `1024`-tail modulus.
-/
theorem exists_primorial_seed_prime_set_of_small_modulus_supply (N J D₀ X₀ X T n : ℕ) (c₀ : ℝ)
    (hN : 0 < N) (hSquarefree : Squarefree N) (hJ : 2 ≤ J) (hn : 0 < n)
    (hsource : 2 ^ (D₀ + n) ≤ (restrictedDivisors N N).card) (hfactor : c₀ * (2 : ℝ) ^ D₀ ≤ 1 / 128)
    (hTbound : (T : ℝ) ≤ c₀ * ((2 ^ (D₀ + n) : ℕ) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ))
    (hHuge : 18000000 ^ 2 ≤ X) (hX₀ : X₀ ≤ X) (hNJ : N ^ J ≤ X)
    (hSupply :
      ∀ Z : ℕ,
        X₀ ≤ Z →
          ∃ E : Finset ℕ,
            E.card ≤ D₀ ∧
              (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
              ∀ m d a : ℕ,
                (m = 1 ∨ m = 4) →
                  0 < d →
                  Nat.Coprime d m →
                  1 < d * m →
                  (d * m) ^ J ≤ Z →
                  Nat.Coprime a (d * m) →
                  (∀ e ∈ E, ¬e ∣ d * m) →
                  (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                    thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a) :
    ∃ E : Finset ℕ,
      E.card ≤ D₀ ∧
        ∃ k ∈ positiveCoprimeParameters 1 (X ^ 3),
          ∃ P : Finset ℕ,
            T < P.card ∧
              ∀ p ∈ P,
                Nat.Prime p ∧
                  p ≤ X ^ 5 ∧
                  p % 1 = 0 ∧
                  ∃
                    d ∈
                      (restrictedDivisors (exceptionalFreePartForModulus N E 1) N).filter
                        (fun d ↦ 1 < d),
                    p = d * k + 1 := by
  have hXtwo : 2 ≤ X := by exact le_trans (by norm_num only) hHuge
  have hXpos : 0 < X := Nat.lt_of_lt_of_le (by norm_num only) hXtwo
  have hJone : 1 ≤ J := le_trans (by norm_num only) hJ
  obtain ⟨E, hEcard, hTheta⟩ :=
    primorial_seed_theta_bounds_of_small_modulus_supply N J D₀ X₀ hN hSquarefree hJ hSupply X hX₀
      hNJ
  let L' := exceptionalFreePartForModulus N E 1
  let D := (restrictedDivisors L' N).filter (fun d ↦ 1 < d)
  let x : ℕ → ℕ := fun d ↦ d * X ^ 3
  let c : ℝ := ((X : ℝ) ^ 3) / (4 * Real.log ((X ^ 5 : ℕ) : ℝ))
  have hLprops := exceptionalFreePartForModulus_properties N E 1 (Nat.ne_of_gt hN) hSquarefree
  have hLdiv : L' ∣ N := hLprops.2.2.1
  have hLne : L' ≠ 0 := by
    intro hzero
    have hzeroDvd : 0 ∣ N := by simpa only [L', hzero] using hLdiv
    exact Nat.ne_of_gt hN (Nat.zero_dvd.mp hzeroDvd)
  have hNNJpow : N ^ 1 ≤ N ^ J := Nat.pow_le_pow_right hN hJone
  have hNNJ : N ≤ N ^ J := by simpa only [Nat.pow_one] using hNNJpow
  have hNX : N ≤ X := le_trans hNNJ hNJ
  have hXfive : 2 ≤ X ^ 5 := by exact le_trans (by norm_num only) (Nat.pow_le_pow_left hXtwo 5)
  have hlogX : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < X ^ 5)
  have hAverage :
    ∀ E' : Finset ℕ,
      E'.card ≤ D₀ →
        (((positiveCoprimeParameters 1 (X ^ 3)).card * T : ℕ) : ℝ) <
          (((X : ℝ) ^ 3) / (4 * Real.log ((X ^ 5 : ℕ) : ℝ))) *
            (((restrictedDivisors (exceptionalFreePartForModulus N E' 1) N).filter
                  (fun d ↦ 1 < d)).card :
              ℝ) := by
    intro E' hE'
    have hCard :=
      exceptional_free_nontrivial_divisor_card_lower_of_source_count N E' D₀ n hN hSquarefree hE'
        hsource
    have hpow : 2 ≤ 2 ^ n := Nat.le_self_pow (Nat.ne_of_gt hn) 2
    have hDpos :
      0 <
        ((restrictedDivisors (exceptionalFreePartForModulus N E' 1) N).filter
            (fun d ↦ 1 < d)).card := by
      omega
    have hThreshold :=
      primorial_seed_threshold_bound_of_exceptional_loss N E' D₀ n T c₀ (Real.log ((X ^ 5 : ℕ) : ℝ))
        hN hSquarefree hE' hn hsource hfactor hlogX hTbound
    exact
      primorial_seed_average_lower_of_divisor_count X T
        ((restrictedDivisors (exceptionalFreePartForModulus N E' 1) N).filter (fun d ↦ 1 < d)) hXtwo
        hDpos hlogX hThreshold
  have hscaleTarget :
    ∀ d,
      ∀ hdD : d ∈ D,
        c ≤
          agpFifthPowerAverageCoefficientOfProgressionBound 0 0 *
            ((x d : ℝ) / (Nat.totient (d * 1) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
    intro d hdD
    have hd' := Finset.mem_filter.mp hdD
    change
      c ≤
        agpFifthPowerAverageCoefficientOfProgressionBound 0 0 *
          (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 1) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ))
    simpa only [c] using
      agp_primorial_seed_average_target X d hXtwo (Nat.lt_trans Nat.zero_lt_one hd'.2)
  have hPos : ∀ d, ∀ hdD : d ∈ D, 0 < d := by
    intro d hdD
    exact Nat.lt_trans Nat.zero_lt_one (Finset.mem_filter.mp hdD).2
  have hCut : ∀ d, ∀ hdD : d ∈ D, x d ≤ d * X ^ 3 + 1 := by
    intro d hdD
    exact Nat.le_add_right (d * X ^ 3) 1
  have hCommon : ∀ d, ∀ hdD : d ∈ D, x d ≤ X ^ 5 := by
    intro d hdD
    have hd' := Finset.mem_filter.mp hdD
    have hdDiv := (mem_restrictedDivisors hLne).mp hd'.1
    have hdN : d ≤ N := Nat.le_of_dvd hN (dvd_trans hdDiv.1 hLdiv)
    have hdX : d ≤ X := le_trans hdN hNX
    have hXpow45 : X ^ 4 ≤ X ^ 5 := Nat.pow_le_pow_right hXpos (by norm_num only)
    change d * X ^ 3 ≤ X ^ 5
    calc
      d * X ^ 3 ≤ X * X ^ 3 := Nat.mul_le_mul_right (X ^ 3) hdX
      _ = X ^ 4 := by ring
      _ ≤ X ^ 5 := hXpow45
  have hXAtLeastTwo : ∀ d, ∀ hdD : d ∈ D, 2 ≤ x d := by
    intro d hdD
    have hd' := Finset.mem_filter.mp hdD
    have hdTwo : 2 ≤ d := Nat.succ_le_iff.mpr hd'.2
    have hXpowPos : 0 < X ^ 3 := Nat.pow_pos hXpos
    have hXpowOne : 1 ≤ X ^ 3 := Nat.succ_le_iff.mpr hXpowPos
    have hmul := Nat.mul_le_mul_left d hXpowOne
    change 2 ≤ d * X ^ 3
    calc
      2 ≤ d := hdTwo
      _ = d * 1 := by rw [Nat.mul_one]
      _ ≤ d * X ^ 3 := by simpa only [Nat.mul_one] using hmul
  have hModulus : ∀ d, ∀ hdD : d ∈ D, (18000000 * d) ^ 2 ≤ x d := by
    intro d hdD
    have hd' := Finset.mem_filter.mp hdD
    have hdDiv := (mem_restrictedDivisors hLne).mp hd'.1
    have hdN : d ≤ N := Nat.le_of_dvd hN (dvd_trans hdDiv.1 hLdiv)
    have hdX : d ≤ X := le_trans hdN hNX
    have hCprod := Nat.mul_le_mul hHuge hdX
    have hCprod' := Nat.mul_le_mul_right d hCprod
    have hXpow23 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hXpos (by norm_num only)
    have hXprod := Nat.mul_le_mul_right d hXpow23
    change (18000000 * d) ^ 2 ≤ d * X ^ 3
    calc
      (18000000 * d) ^ 2 = 18000000 ^ 2 * d ^ 2 := by rw [Nat.mul_pow]
      _ = (18000000 ^ 2 * d) * d := by ring
      _ ≤ (X * X) * d := hCprod'
      _ ≤ X ^ 3 * d := by simpa only [pow_two] using hXprod
      _ = d * X ^ 3 := Nat.mul_comm _ _
  have hTheta' :
    ∀ d,
      ∀ hdD : d ∈ D,
        ((x d : ℝ) / (2 * (Nat.totient d : ℝ))) ≤
          thetaInProgressionReal (x d : ℝ) (d * 1)
            (progressionCoprimeResidue d 1 1 (Nat.coprime_one_right d)) := by
    intro d hdD
    simpa only [x, Nat.mul_one] using hTheta d hdD
  obtain ⟨k, hk, P, hPcard, hP⟩ :=
    exists_primorial_seed_prime_set_from_theta D x (X ^ 5) (X ^ 3) T c hXfive hPos hCut hCommon
      hXAtLeastTwo hModulus hTheta' hscaleTarget (hAverage E hEcard)
  exact ⟨E, hEcard, k, hk, P, hPcard, hP⟩

/--
Inputs: a primorial seed count, its finite-divisor source bound, the small-modulus theta supply,
and the cutoff-1024 prime-count estimate.

Claim: a seed set of exactly `T + 1` primes yields a squarefree 1024-tail modulus with reciprocal
prime sum at most `1 / 1024`, Carmichael lower bound at least `3`, and the divisor-form seed data.

Proof: extract the initial prime set from theta, choose a subset of the required size, and apply
the arbitrary-cutoff seed-modulus and P2 lower-bound theorems.

Role: connects the primorial theta average to the full-divisor P2 auxiliary-modulus constructor.
-/
theorem exists_primorial_seed_tail_modulus_of_small_modulus_supply (N J D₀ X₀ X T n : ℕ) (c₀ : ℝ)
    (hN : 0 < N) (hSquarefree : Squarefree N) (hJ : 2 ≤ J) (hn : 0 < n)
    (hsource : 2 ^ (D₀ + n) ≤ (restrictedDivisors N N).card) (hfactor : c₀ * (2 : ℝ) ^ D₀ ≤ 1 / 128)
    (hTbound : (T : ℝ) ≤ c₀ * ((2 ^ (D₀ + n) : ℕ) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ))
    (hHuge : 18000000 ^ 2 ≤ X) (hX₀ : X₀ ≤ X) (hNJ : N ^ J ≤ X)
    (hSupply :
      ∀ Z : ℕ,
        X₀ ≤ Z →
          ∃ E : Finset ℕ,
            E.card ≤ D₀ ∧
              (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
              ∀ m d a : ℕ,
                (m = 1 ∨ m = 4) →
                  0 < d →
                  Nat.Coprime d m →
                  1 < d * m →
                  (d * m) ^ J ≤ Z →
                  Nat.Coprime a (d * m) →
                  (∀ e ∈ E, ¬e ∣ d * m) →
                  (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                    thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a)
    (h1024 : 2 * Nat.primeCounting (1024 * (T + 1)) ≤ T + 1) :
    ∃ E : Finset ℕ,
      E.card ≤ D₀ ∧
        ∃ k,
          k ∈ positiveCoprimeParameters 1 (X ^ 3) ∧
            ∃ (S : Finset ℕ) (L : ℕ),
              S.card = T + 1 ∧
                (∀ p ∈ S, Nat.Prime p ∧ p ≤ X ^ 5 ∧ ∃ d, d ∣ N ∧ p = d * k + 1) ∧
                L = (S.filter (fun p ↦ 1024 * S.card < p)).prod id ∧
                Squarefree L ∧
                L.primeFactors = S.filter (fun p ↦ 1024 * S.card < p) ∧
                (∑ p ∈ (L.primeFactors : Finset ℕ), (p : ℝ)⁻¹) ≤ (1 / 1024 : ℝ) ∧
                ArithmeticFunction.carmichael L ∣ k * N ∧
                S.card ≤ 2 * (S.filter (fun p ↦ 1024 * S.card < p)).card ∧
                L ≤ (X ^ 5) ^ (T + 1) ∧
                (∀ r, r ∣ L → Nat.Prime r → r ≤ X ^ 5) ∧
                ArithmeticFunction.carmichael L ≤ (X ^ 5) ^ 2 ∧
                2 < L ∧ 3 ≤ ArithmeticFunction.carmichael L := by
  obtain ⟨E, hEcard, k, hk, P, hPcard, hP⟩ :=
    exists_primorial_seed_prime_set_of_small_modulus_supply N J D₀ X₀ X T n c₀ hN hSquarefree hJ hn
      hsource hfactor hTbound hHuge hX₀ hNJ hSupply
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (s := P) (n := T + 1) (Nat.succ_le_of_lt hPcard)
  have hLprops := exceptionalFreePartForModulus_properties N E 1 (Nat.ne_of_gt hN) hSquarefree
  have hLdiv : exceptionalFreePartForModulus N E 1 ∣ N := hLprops.2.2.1
  have hLne : exceptionalFreePartForModulus N E 1 ≠ 0 := by
    intro hzero
    have hzeroDvd : 0 ∣ N := by simpa only [hzero] using hLdiv
    exact Nat.ne_of_gt hN (Nat.zero_dvd.mp hzeroDvd)
  have hprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    exact (hP p (hSsub hp)).1
  have hseed : ∀ p ∈ S, ∃ d, d ∣ N ∧ p = d * k + 1 := by
    intro p hp
    rcases hP p (hSsub hp) with ⟨_, _, _, d, hdD, hEq⟩
    have hd' := Finset.mem_filter.mp hdD
    have hdDiv := (mem_restrictedDivisors hLne).mp hd'.1
    exact ⟨d, dvd_trans hdDiv.1 hLdiv, hEq⟩
  have hSpos : 0 < S.card := by
    rw [hScard]; exact Nat.succ_pos T
  have hcount : 2 * Nat.primeCounting (1024 * S.card) ≤ S.card := by
    rw [hScard]
    exact h1024
  let Ptail := S.filter (fun p ↦ 1024 * S.card < p)
  let L := Ptail.prod id
  obtain ⟨hSquarefreeL, hPrimeFactorsL, hReciprocalL, hCarmichaelL, hTailCard⟩ :=
    seed_prime_tail_auxiliary_modulus_data_of_cutoff S k N 1024 (by norm_num only) hprime hseed
      hSpos hcount
  have hP2 :=
    seed_prime_tail_p2_lower_bounds_of_cutoff S 1024 (by norm_num only : 4 < 1024) hprime hSpos
      hcount
  have hP2' : 2 < L ∧ 3 ≤ ArithmeticFunction.carmichael L := by simpa only [L, Ptail] using hP2
  have hSdata : ∀ p ∈ S, Nat.Prime p ∧ p ≤ X ^ 5 ∧ ∃ d, d ∣ N ∧ p = d * k + 1 := by
    intro p hp
    rcases hP p (hSsub hp) with ⟨hprimeP, hboundP, _, d, hdD, hEq⟩
    have hd' := Finset.mem_filter.mp hdD
    have hdDiv := (mem_restrictedDivisors hLne).mp hd'.1
    exact ⟨hprimeP, hboundP, d, dvd_trans hdDiv.1 hLdiv, hEq⟩
  have hqone : 1 ≤ X ^ 5 := by
    have hXpos : 0 < X := Nat.lt_of_lt_of_le (by norm_num only) hHuge
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos hXpos))
  have hTailCardLe : Ptail.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hLbound : L ≤ (X ^ 5) ^ (T + 1) := by
    change Ptail.prod id ≤ (X ^ 5) ^ (T + 1)
    calc
      Ptail.prod id ≤ (X ^ 5) ^ Ptail.card := by
        apply Finset.prod_le_pow_card
        intro p hp
        exact (hSdata p (Finset.mem_filter.mp hp).1).2.1
      _ ≤ (X ^ 5) ^ S.card := Nat.pow_le_pow_right hqone hTailCardLe
      _ = (X ^ 5) ^ (T + 1) := by rw [hScard]
  have hfactorTail : ∀ r, r ∣ L → Nat.Prime r → r ≤ X ^ 5 := by
    intro r hr hprimeR
    have hmem : r ∈ L.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hprimeR, hr, Nat.ne_of_gt (lt_trans (by norm_num only) hP2'.1)⟩
    rw [hPrimeFactorsL] at hmem
    exact (hSdata r (Finset.mem_filter.mp hmem).1).2.1
  have hNleX : N ≤ X := by
    have hpow : N ^ 1 ≤ N ^ J := Nat.pow_le_pow_right hN (by omega)
    exact le_trans (by simpa only [Nat.pow_one] using hpow) hNJ
  have hkX : k ≤ X ^ 3 := (mem_positiveCoprimeParameters.mp hk).2.1
  have hkn : k * N ≤ (X ^ 5) ^ 2 := by
    calc
      k * N ≤ X ^ 3 * X := Nat.mul_le_mul hkX hNleX
      _ ≤ X ^ 5 * X ^ 5 := by
        exact
          Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by norm_num only))
            (Nat.le_self_pow (by norm_num only) X)
      _ = (X ^ 5) ^ 2 := by rw [pow_two]
  have hkpos : 0 < k := Nat.succ_le_iff.mp (mem_positiveCoprimeParameters.mp hk).1
  have hLambdaBound : ArithmeticFunction.carmichael L ≤ (X ^ 5) ^ 2 :=
    le_trans (Nat.le_of_dvd (Nat.mul_pos hkpos hN) hCarmichaelL) hkn
  refine ⟨E, hEcard, k, hk, S, L, hScard, hSdata, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa only [L, Ptail] using hSquarefreeL
  · simpa only [L, Ptail] using hPrimeFactorsL
  · have hInv : (1024 : ℝ)⁻¹ = 1 / 1024 := by norm_num only
    simpa only [L, Ptail] using le_trans hReciprocalL (le_of_eq hInv)
  · simpa only [L, Ptail] using hCarmichaelL
  · simpa only [L, Ptail] using hTailCard
  · exact hLbound
  · exact hfactorTail
  · exact hLambdaBound
  · exact hP2'.1
  · exact hP2'.2

/--
Inputs: a primorial cutoff, the exceptional-modulus budget and exponent, a
small-modulus theta supply, and the strict initial P2 count margin.

Claim: the primorial and margin determine the source count and threshold needed
to construct the finite set of initial seed primes.

Proof: derive the source-count and threshold pair from the primorial margin,
then apply the fixed-scale theta seed theorem.

Role: joins the P2 scale's initial-count output to the seed-prime construction.
-/
theorem exists_primorial_seed_prime_set_of_count_margin (z J D₀ X₀ X T : ℕ) (c₀ : ℝ) (hJ : 2 ≤ J)
    (hD : D₀ < Nat.primeCounting z) (hfactor : c₀ * (2 : ℝ) ^ D₀ ≤ 1 / 128)
    (hmargin :
      (T : ℝ) < reliableProp15Coefficient c₀ 1 (X ^ 5) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ))
    (hHuge : 18000000 ^ 2 ≤ X) (hX₀ : X₀ ≤ X)
    (hNJ : ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id) ^ J ≤ X)
    (hSupply :
      ∀ Z : ℕ,
        X₀ ≤ Z →
          ∃ E : Finset ℕ,
            E.card ≤ D₀ ∧
              (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
              ∀ m d a : ℕ,
                (m = 1 ∨ m = 4) →
                  0 < d →
                  Nat.Coprime d m →
                  1 < d * m →
                  (d * m) ^ J ≤ Z →
                  Nat.Coprime a (d * m) →
                  (∀ e ∈ E, ¬e ∣ d * m) →
                  (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                    thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a) :
    ∃ E : Finset ℕ,
      E.card ≤ D₀ ∧
        ∃ k ∈ positiveCoprimeParameters 1 (X ^ 3),
          ∃ P : Finset ℕ,
            T < P.card ∧
              ∀ p ∈ P,
                Nat.Prime p ∧
                  p ≤ X ^ 5 ∧
                  p % 1 = 0 ∧
                  ∃
                    d ∈
                      (restrictedDivisors
                            (exceptionalFreePartForModulus
                              ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id) E 1)
                            ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id)).filter
                        (fun d ↦ 1 < d),
                    p = d * k + 1 := by
  let N := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id
  have hN : 0 < N := PseudoPrime.NumberTheory.PrimeProducts.primeProductLE_pos z
  have hdata := PseudoPrime.NumberTheory.PrimeProducts.primeProductLE_data z
  obtain ⟨n, hn, hsource, hTbound⟩ :=
    primorial_seed_initial_count_data_of_margin z D₀ (X ^ 5) T c₀ hD hmargin
  exact
    exists_primorial_seed_prime_set_of_small_modulus_supply N J D₀ X₀ X T n c₀ hN hdata.1 hJ hn
      hsource hfactor hTbound hHuge hX₀ hNJ hSupply

/--
Inputs: a primorial cutoff, its initial P2 count margin, the cutoff-1024
prime-count estimate, and the fixed-scale small-modulus theta supply.

Claim: these data produce the primorial seed set and its squarefree tail
modulus, including the reciprocal-prime-sum and Carmichael bounds.

Proof: derive the finite-divisor source count and threshold from the primorial
margin, then apply the general cutoff tail construction.

Role: connects one P2 scale choice directly to the full seed-tail interface.
-/
theorem exists_primorial_seed_tail_modulus_of_count_margin (z J D₀ X₀ X T : ℕ) (c₀ : ℝ) (hJ : 2 ≤ J)
    (hD : D₀ < Nat.primeCounting z) (hfactor : c₀ * (2 : ℝ) ^ D₀ ≤ 1 / 128)
    (hmargin :
      (T : ℝ) < reliableProp15Coefficient c₀ 1 (X ^ 5) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ))
    (hHuge : 18000000 ^ 2 ≤ X) (hX₀ : X₀ ≤ X)
    (hNJ : ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id) ^ J ≤ X)
    (hSupply :
      ∀ Z : ℕ,
        X₀ ≤ Z →
          ∃ E : Finset ℕ,
            E.card ≤ D₀ ∧
              (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
              ∀ m d a : ℕ,
                (m = 1 ∨ m = 4) →
                  0 < d →
                  Nat.Coprime d m →
                  1 < d * m →
                  (d * m) ^ J ≤ Z →
                  Nat.Coprime a (d * m) →
                  (∀ e ∈ E, ¬e ∣ d * m) →
                  (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                    thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a)
    (h1024 : 2 * Nat.primeCounting (1024 * (T + 1)) ≤ T + 1) :
    ∃ E : Finset ℕ,
      E.card ≤ D₀ ∧
        ∃ k,
          k ∈ positiveCoprimeParameters 1 (X ^ 3) ∧
            ∃ (S : Finset ℕ) (L : ℕ),
              S.card = T + 1 ∧
                (∀ p ∈ S,
                  Nat.Prime p ∧
                    p ≤ X ^ 5 ∧
                    ∃ d,
                      d ∣ ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id) ∧
                        p = d * k + 1) ∧
                L = (S.filter (fun p ↦ 1024 * S.card < p)).prod id ∧
                Squarefree L ∧
                L.primeFactors = S.filter (fun p ↦ 1024 * S.card < p) ∧
                (∑ p ∈ (L.primeFactors : Finset ℕ), (p : ℝ)⁻¹) ≤ (1 / 1024 : ℝ) ∧
                ArithmeticFunction.carmichael L ∣
                  k * ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id) ∧
                S.card ≤ 2 * (S.filter (fun p ↦ 1024 * S.card < p)).card ∧
                L ≤ (X ^ 5) ^ (T + 1) ∧
                (∀ r, r ∣ L → Nat.Prime r → r ≤ X ^ 5) ∧
                ArithmeticFunction.carmichael L ≤ (X ^ 5) ^ 2 ∧
                2 < L ∧ 3 ≤ ArithmeticFunction.carmichael L := by
  let N := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id
  have hN : 0 < N := PseudoPrime.NumberTheory.PrimeProducts.primeProductLE_pos z
  have hdata := PseudoPrime.NumberTheory.PrimeProducts.primeProductLE_data z
  obtain ⟨n, hn, hsource, hTbound⟩ :=
    primorial_seed_initial_count_data_of_margin z D₀ (X ^ 5) T c₀ hD hmargin
  exact
    exists_primorial_seed_tail_modulus_of_small_modulus_supply N J D₀ X₀ X T n c₀ hN hdata.1 hJ hn
      hsource hfactor hTbound hHuge hX₀ hNJ hSupply h1024

end PseudoPrime.AnalyticNumberTheory.AGP
