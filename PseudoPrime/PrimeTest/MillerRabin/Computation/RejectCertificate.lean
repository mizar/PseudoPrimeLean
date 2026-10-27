/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition

/-! # Explicit bounded-decomposition rejection certificates for Miller--Rabin -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Split at most fuel factors of two from m, returning their count and the residual factor.
This executable proposal is independently checked for decomposition and oddness.
It avoids using an opaque canonical decomposition during finite certificate evaluation. -/
def mrCertificateSplitTwo (fuel m : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (0, m)
  | fuel + 1 =>
    if m % 2 = 0 then
      let (s, d) := mrCertificateSplitTwo fuel (m / 2)
      (s + 1, d)
    else (0, m)

/-- Check a proposed n-1 = 2^s d decomposition with odd d and rejecting binary modular powers.
The base a is arbitrary; the returned Boolean is validated by the soundness theorem.
Finite classifications use this to certify genuine failures of the strong test. -/
def mrCertificateRejectData (n a s d : ℕ) : Bool :=
  decide (n - 1 = 2 ^ s * d ∧ Odd d ∧ zmodPow n a d ≠ 1) &&
    (List.range s).all (fun j => decide (zmodPow n a (2 ^ j * d) ≠ -1))

/-- Propose a decomposition using seventeen division steps and check all rejection inequalities.
The checker remains sound for every modulus because it verifies the proposed decomposition.
Seventeen steps suffice for the finite fitting investigation through 100000. -/
def mrCertificateReject (n a : ℕ) : Bool :=
  let (s, d) := mrCertificateSplitTwo 17 (n - 1)
  mrCertificateRejectData n a s d

/-- For n > 1, a successful decomposition-and-power certificate proves that base a fails.
Identify the canonical two-adic pair using oddness and transport each modular power inequality.
This connects the finite computational checker to the existing strong-pass specification. -/
theorem mrCertificateRejectData_sound {n a s d : ℕ} (hn : 1 < n)
    (hcheck : mrCertificateRejectData n a s d = true) : ¬StrongMillerRabinPass n (a : ZMod n) := by
  rw [mrCertificateRejectData, Bool.and_eq_true] at hcheck
  obtain ⟨hbase, hsteps⟩ := hcheck
  obtain ⟨hdecomp, hdOdd, hodd⟩ := of_decide_eq_true hbase
  have hdvd : ¬2 ∣ d := fun hd => (Nat.not_even_iff_odd.mpr hdOdd) (even_iff_two_dvd.mpr hd)
  have hmax := Nat.maxPowDvdDiv_of_pow_mul_eq (Nat.sub_ne_zero_of_lt hn) hdecomp.symm hdvd
  have hs : padicValNat 2 (n - 1) = s :=
    (Nat.fst_maxPowDvdDiv 2 (n - 1)).symm.trans (congrArg Prod.fst hmax)
  have hd : Nat.divMaxPow (n - 1) 2 = d :=
    (Nat.snd_maxPowDvdDiv 2 (n - 1)).symm.trans (congrArg Prod.snd hmax)
  apply not_strongMillerRabinPass_iff.mpr
  rw [hs, hd]
  refine ⟨?_, ?_⟩
  · simpa only [zmodPow_eq_pow] using hodd
  · intro j hj
    have hstep := of_decide_eq_true (List.all_eq_true.mp hsteps j (List.mem_range.mpr hj))
    simpa only [zmodPow_eq_pow] using hstep

/-- For n > 1, the executable bounded-decomposition checker proves a genuine base failure.
Apply the data checker soundness to the proposed pair, without assuming its correctness.
Finite witness consumers use this specification bridge. -/
theorem mrCertificateReject_sound {n a : ℕ} (hn : 1 < n) (hcheck : mrCertificateReject n a = true) :
    ¬StrongMillerRabinPass n (a : ZMod n) := by exact mrCertificateRejectData_sound hn hcheck

end PseudoPrime.PrimeTest
