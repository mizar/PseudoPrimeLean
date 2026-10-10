/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetPrimeBounds
public import PseudoPrime.LLS.Corollary11SmallBounds
public import PseudoPrime.NumberTheory.TotientComputation

/-!
# Finite residue certificates for Corollary 1.2

A checked witness function gives a prime in every unit residue class.
Sound Boolean prime tests allow primality proofs to be shared across moduli.
The integer caps imply the paper's real bound, which then passes to the least prime.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Integer witness cap below the totient-logarithm bound for moduli at least four.
Use six for modulus four, twice the totient square for five and six, and three times
that square for larger moduli. Euler's product computes the totient without enumerating
coprime residues. Finite checks require no logarithm computation. -/
def residuePrimeCap (q : ℕ) : ℕ :=
  if q = 4 then 6
  else
    if q < 7 then 2 * NumberTheory.totientFromPrimeFactors q ^ 2
    else 3 * NumberTheory.totientFromPrimeFactors q ^ 2

/-- A witness function certifies a prime in every reduced residue class.
For each representative below the modulus, coprimality requires primality, the correct
remainder, and the integer cap. Nonunit representatives impose no condition.
The certificate implies the least-prime bound of Corollary 1.2. -/
def residuePrimeCertificateChecked (q : ℕ) (witness : ℕ → ℕ) : Prop :=
  ∀ a : Fin q,
    a.val.Coprime q →
      (witness a.val).Prime ∧ witness a.val % q = a.val ∧ witness a.val ≤ residuePrimeCap q

/-- Boolean verification of a prime witness for every reduced residue class.
The prime test is supplied separately and must have a soundness proof when reflecting
this check. Remainders and the integer cap are checked by finite arithmetic, using
subtraction for comparison. The checker can be reduced in the kernel. -/
def residuePrimeCertificateCheck (q : ℕ) (isPrime : ℕ → Bool) (witness : ℕ → ℕ) : Bool :=
  (List.range q).all fun a ↦
    let p := witness a
    (!(a.gcd q == 1)) || (isPrime p && (p % q == a) && (p - residuePrimeCap q == 0))

/-- A sound prime test and a successful finite check give a residue certificate.
Extract the check at each coprime representative, reflect its remainder and cap,
and apply soundness of the supplied prime test. All generated checks share this lemma. -/
theorem residuePrimeCertificateCheck_sound {q : ℕ} {isPrime : ℕ → Bool} {witness : ℕ → ℕ}
    (hPrime : ∀ p, isPrime p = true → p.Prime)
    (h : residuePrimeCertificateCheck q isPrime witness = true) :
    residuePrimeCertificateChecked q witness := by
  intro a ha
  have hk := List.all_eq_true.mp h a.val (List.mem_range.mpr a.isLt)
  have hg : a.val.gcd q = 1 := Nat.coprime_iff_gcd_eq_one.mp ha
  have he :
    (isPrime (witness a.val) && (witness a.val % q == a.val) &&
        (witness a.val - residuePrimeCap q == 0)) =
      true := by
    simpa only [hg, beq_self_eq_true, Bool.not_true, Bool.false_or] using hk
  have hp :
    isPrime (witness a.val) = true ∧
      witness a.val % q = a.val ∧ witness a.val ≤ residuePrimeCap q := by
    simpa only [Bool.and_eq_true, beq_iff_eq, Nat.sub_eq_zero_iff_le, and_assoc] using he
  exact ⟨hPrime _ hp.1, hp.2⟩

/-- Search a progression for at most the given number of terms with a supplied
Boolean prime test. Return the first accepted term, or zero if the fuel is exhausted.
No completeness is assumed: the separate residue checker verifies the returned term's
primality, congruence, and cap before it is used in the paper bound. -/
def residuePrimeSearch (isPrime : ℕ → Bool) (q a fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | n + 1 => if isPrime a then a else residuePrimeSearch isPrime q (a + q) n

/-- For a nonzero modulus, a certificate gives a bounded prime for each unit.
Use the unit's canonical representative and its coprimality, then injectivity of
representatives to convert the checked remainder to equality in `ZMod`.
The witness retains its certified integer cap. -/
theorem residuePrimeCertificateChecked_sound {q : ℕ} [NeZero q] {witness : ℕ → ℕ}
    (h : residuePrimeCertificateChecked q witness) (a : (ZMod q)ˣ) :
    ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = (a : ZMod q) ∧ p ≤ residuePrimeCap q := by
  let r : Fin q := ⟨(a : ZMod q).val, ZMod.val_lt (a : ZMod q)⟩
  have hu : IsUnit (r.val : ZMod q) := by
    change IsUnit ((a : ZMod q).val : ZMod q)
    rw [ZMod.natCast_zmod_val]
    exact a.isUnit
  obtain ⟨hp, hm, hb⟩ := h r ((ZMod.isUnit_iff_coprime r.val q).mp hu)
  refine ⟨witness r.val, hp, ?_, hb⟩
  apply ZMod.val_injective q
  rw [ZMod.val_natCast]
  exact hm

/-- For a modulus at least four, the integer cap implies the paper's real bound.
The modulus-four case uses the lower bound for `log 2`; larger moduli use lower bounds
by two and three for the logarithmic square. Multiplication by the totient square
converts finite certificate bounds to the bound of Corollary 1.2. -/
theorem residuePrimeCap_le_totient_log_sq {q : ℕ} (hq : 4 ≤ q) :
    (residuePrimeCap q : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  by_cases h4 : q = 4
  · subst q
    have he := Real.log_pow (2 : ℝ) 2
    norm_num only at he
    have hl := Real.log_two_gt_d9
    change (6 : ℝ) ≤ ((Nat.totient 4 : ℝ) * Real.log 4) ^ 2
    have hφ : Nat.totient 4 = 2 := by decide
    rw [hφ]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [he, hl, sq_nonneg (Real.log 4 - 1.38)]
  · have h5 : 5 ≤ q := Nat.succ_le_of_lt (lt_of_le_of_ne hq (Ne.symm h4))
    by_cases h7 : q < 7
    · have hs := LLS.two_lt_log_sq h5
      have hb := mul_le_mul_of_nonneg_left hs.le (sq_nonneg (q.totient : ℝ))
      simpa only [residuePrimeCap, NumberTheory.totientFromPrimeFactors_eq_totient, ite_eq_right h4,
        ite_eq_left h7, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, mul_comm] using hb
    · have hs := LLS.three_lt_log_sq (Nat.le_of_not_gt h7)
      have hb := mul_le_mul_of_nonneg_left hs.le (sq_nonneg (q.totient : ℝ))
      simpa only [residuePrimeCap, NumberTheory.totientFromPrimeFactors_eq_totient, ite_eq_right h4,
        ite_eq_right h7, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, mul_comm] using hb

/-- For a nonzero modulus at least four, a certificate bounds the least prime
in every unit residue class by the totient-logarithm square, without GRH.
Convert the certified witness cap to the real bound, then minimize the prime set.
This connects the finite checks to the bounded-modulus part of Corollary 1.2. -/
theorem exists_least_prime_in_residue_le_of_certificate {q : ℕ} [NeZero q] {witness : ℕ → ℕ}
    (hq : 4 ≤ q) (h : residuePrimeCertificateChecked q witness) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  obtain ⟨p, hp, ha, hb⟩ := residuePrimeCertificateChecked_sound h a
  exact
    exists_least_prime_in_residue_le a
      ⟨p, hp, ha, (Nat.cast_le.mpr hb).trans (residuePrimeCap_le_totient_log_sq hq)⟩

/-- Check consecutive moduli with a common prime test and search fuel.
Every modulus in the finite interval must pass the residue checker. This groups
computations so the certified prime tree can be shared within a kernel check. -/
def residuePrimeBlockCheck (s w fuel : ℕ) (isPrime : ℕ → Bool) : Bool :=
  (List.range w).all fun k ↦
    residuePrimeCertificateCheck (s + k) isPrime (fun a ↦ residuePrimeSearch isPrime (s + k) a fuel)

/-- Every modulus of a finite interval has a checked prime witness function.
The witness is progression search with the supplied prime test and fuel.
This proposition is the interface between block computations and the paper bound. -/
def residuePrimeBlockChecked (s w fuel : ℕ) (isPrime : ℕ → Bool) : Prop :=
  ∀ k : Fin w,
    residuePrimeCertificateChecked (s + k.val)
      (fun a ↦ residuePrimeSearch isPrime (s + k.val) a fuel)

/-- A sound prime test reflects a successful block check into residue certificates.
Extract each position of the finite conjunction and apply the single-modulus reflection.
The result is independent of how the Boolean prime test is implemented. -/
theorem residuePrimeBlockCheck_sound {s w fuel : ℕ} {isPrime : ℕ → Bool}
    (hPrime : ∀ p, isPrime p = true → p.Prime)
    (h : residuePrimeBlockCheck s w fuel isPrime = true) :
    residuePrimeBlockChecked s w fuel isPrime := by
  intro k
  exact
    residuePrimeCertificateCheck_sound hPrime
      (List.all_eq_true.mp h k.val (List.mem_range.mpr k.isLt))

/-- Consecutive checked blocks of sixteen moduli starting at four give the bound
of Corollary 1.2 throughout their union. Division with remainder selects the block
and its offset; the certificate-to-least-prime theorem then supplies the conclusion.
No GRH assumption is needed for this bounded range. -/
theorem exists_least_prime_in_residue_le_of_blocks {n fuel q : ℕ} [NeZero q] {isPrime : ℕ → Bool}
    (h : ∀ b : Fin n, residuePrimeBlockChecked (4 + 16 * b.val) 16 fuel isPrime) (hq : 4 ≤ q)
    (hb : q < 4 + 16 * n) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have hsub : q - 4 < 16 * n := Nat.sub_lt_left_of_lt_add hq hb
  have hdiv : (q - 4) / 16 < n :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).mpr (by simpa only [Nat.mul_comm] using hsub)
  let b : Fin n := ⟨(q - 4) / 16, hdiv⟩
  let k : Fin 16 := ⟨(q - 4) % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩
  have he : 4 + 16 * b.val + k.val = q := by
    change 4 + 16 * ((q - 4) / 16) + (q - 4) % 16 = q
    rw [Nat.add_assoc, Nat.div_add_mod, Nat.add_sub_of_le hq]
  have hc := h b k
  rw [he] at hc
  exact exists_least_prime_in_residue_le_of_certificate hq hc a

end PseudoPrime.LLS.PaperStatements
