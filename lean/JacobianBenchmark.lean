import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
/- Adapted from Kim Morrison, Lean FRO, hex-dev, Apache-2.0,
revision 3a1b9813b1d1876ae0c89f5cfc20da05547bd854.
Changes: compute and verify inverses, elementary point count, standalone Mathlib. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





/-!
# Elliptic curve arithmetic before primality is known

An ECPP proof calculates with `y² = x³ + a*x + b` modulo the integer `n`
whose primality is still to be established. Since `n` may be composite,
a nonzero denominator need not be invertible. Each addition that divides
uses a supplied inverse and verifies it by modular multiplication.

Successful additions return coordinates reduced modulo `n`. The Mathlib
companion proves that these calculations agree with the elliptic curve
group law after reduction modulo every prime divisor of `n`.
-/

namespace Hex.ECPP

/-- Coordinates used when checking a primality certificate's scalar
multiplication: either the point at infinity or a finite pair of natural
numbers. Curve membership and reduced coordinates are checked separately. -/
inductive Point where
  | infinity
  | affine (x y : Nat)
deriving Repr, BEq, DecidableEq

/-- Natural subtraction interpreted modulo `n`, for canonical operands. -/

def modSub (n a b : Nat) : Nat := (a % n + n - b % n) % n

/-- The equation of the short Weierstrass curve. -/

def onCurve (n a b x y : Nat) : Bool :=
  (y * y) % n == (x * x * x + a * x + b) % n

/-- A canonical point has both coordinates below the modulus. -/

def Point.canonical (n : Nat) : Point → Bool
  | .infinity => true
  | .affine x y => x < n && y < n

/-- Infinity belongs to every short curve; finite points satisfy its equation. -/

def Point.onCurve (n a b : Nat) : Point → Bool
  | .infinity => true
  | .affine x y => Hex.ECPP.onCurve n a b x y

/-- Complete one division branch, consuming exactly one inverse witness. -/

def addWithInverse (n x₁ y₁ x₂ d v : Nat)
    (inverses : List Nat) : Option (Point × List Nat) := do
  let u := (Int.gcdA (d : ℤ) (n : ℤ) % (n : ℤ)).toNat
  let rest := inverses
  if !(u < n && d * u % n == 1) then none
  else
    let slope := v * u % n
    let x₃ := modSub n (modSub n (slope * slope % n) x₁) x₂
    let y₃ := modSub n (slope * (modSub n x₁ x₃) % n) y₁
    some (.affine x₃ y₃, rest)

/-- Partial affine addition with explicit inverse witnesses. -/

def add? (n a : Nat) (P Q : Point) (inverses : List Nat) :
    Option (Point × List Nat) :=
  match P, Q with
  | .infinity, Q => some (Q, inverses)
  | P, .infinity => some (P, inverses)
  | .affine x₁ y₁, .affine x₂ y₂ =>
    if x₁ == x₂ then
      if (y₁ + y₂) % n == 0 then some (.infinity, inverses)
      else if y₁ == y₂ then
        addWithInverse n x₁ y₁ x₂ (2 * y₁ % n)
          ((3 * x₁ * x₁ + a) % n) inverses
      else none
    else
      addWithInverse n x₁ y₁ x₂ (modSub n x₂ x₁)
        (modSub n y₂ y₁) inverses

/-- Replay accepts only canonical points on the supplied curve after each
addition. This makes both arithmetic invariants local, executable checks. -/

def checkedAdd? (n a b : Nat) (P Q : Point) (inverses : List Nat) :
    Option (Point × List Nat) := do
  let (R, rest) ← add? n a P Q inverses
  if R.canonical n && R.onCurve n a b then some (R, rest) else none

/-- Accepted checked additions satisfy the raw branch and both local arithmetic invariants. -/
theorem checkedAdd_facts {n a b : Nat} {P Q R : Point}
    {ws rest : List Nat}
    (h : checkedAdd? n a b P Q ws = some (R, rest)) :
    add? n a P Q ws = some (R, rest) ∧
      R.canonical n = true ∧ R.onCurve n a b = true := by
  unfold checkedAdd? at h
  cases hadd : add? n a P Q ws with
  | none => simp [hadd] at h
  | some pair =>
      rcases pair with ⟨S, tail⟩
      simp [hadd] at h
      rcases h with ⟨⟨hcan, hcurve⟩, rfl, rfl⟩
      exact ⟨rfl, hcan, hcurve⟩

/-- Modular subtraction returns a canonical residue for a positive modulus. -/
theorem modSub_lt {n a b : Nat} (hn : 0 < n) : modSub n a b < n := by
  exact Nat.mod_lt _ hn

/-- A successful division branch used exactly the next checked witness. -/
theorem addWithInverse_spec {n x₁ y₁ x₂ d v : Nat}
    {ws rest : List Nat} {R : Point}
    (h : addWithInverse n x₁ y₁ x₂ d v ws = some (R, rest)) :
    ∃ u, ws = rest ∧ u < n ∧ d * u % n = 1 ∧
      R = .affine
        (modSub n (modSub n ((v * u % n) * (v * u % n) % n) x₁) x₂)
        (modSub n ((v * u % n) *
          (modSub n x₁ (modSub n (modSub n ((v * u % n) * (v * u % n) % n) x₁) x₂)) % n) y₁) := by
  let u := (Int.gcdA (d : ℤ) (n : ℤ) % (n : ℤ)).toNat
  by_cases hu : u < n ∧ d * u % n = 1
  · have hbool : (u < n && d * u % n == 1) = true := by
      simp [hu.1, hu.2]
    change (if !(u < n && d * u % n == 1) then none else _) = _ at h
    simp only [hbool, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨u, rfl, hu.1, hu.2, rfl⟩
  · have hbool : (u < n && d * u % n == 1) = false := by
      apply Bool.eq_false_of_ne_true
      intro htrue
      simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at htrue
      exact hu htrue
    change (if !(u < n && d * u % n == 1) then none else _) = _ at h
    simp [hbool] at h

end Hex.ECPP
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






/-!
# Verifying multiplication of an elliptic curve point

An elliptic curve primality certificate needs a finite point `Q` with
`q • Q = O`, where `q` is the smaller prime certified by the next link in
the chain. We calculate this multiple by binary doubling and addition.
Each division uses a supplied modular inverse, checked by multiplication;
the certificate cannot choose a different sequence of scalar bits.

The final size test is the exact integer form of
`q > (n^(1/4) + 1)²`, the strict inequality used with Hasse's bound.
-/

namespace Hex.ECPP

/-- Replay the remaining `bits` of `q`, from high index to low index. -/

def replayBits (n a b q : Nat) (Q : Point) :
    (bits : Nat) → Point → List Nat → Option (Point × List Nat)
  | 0, R, inverses => some (R, inverses)
  | bits + 1, R, inverses => do
      let (D, inverses) ← checkedAdd? n a b R R inverses
      let (S, inverses) ←
        if q.testBit bits then checkedAdd? n a b D Q inverses
        else some (D, inverses)
      replayBits n a b q Q bits S inverses

/-- Calculate `q • Q` by binary doubling and addition modulo `n`, verifying
the supplied inverse for every division. Return the resulting point and any
unused inverses, or `none` if a required arithmetic check fails. -/

def replay (n a b q : Nat) (Q : Point) (inverses : List Nat) :
    Option (Point × List Nat) :=
  replayBits n a b q Q ((Nat.log2 q + 1)) .infinity inverses

/-- Verify `q • Q = O` modulo `n`, with every supplied inverse used exactly
once. The certificate for `q` and the curve's nonsingularity are checked
separately by `check`. -/

def replayDone (n a b q : Nat) (Q : Point) (inverses : List Nat) : Bool :=
  match replay n a b q Q inverses with
  | some (.infinity, []) => true
  | _ => false

/-- Every point returned by an accepted replay prefix is a canonical point
on the supplied curve. The induction follows the actual bit schedule. -/
theorem replayBits_facts {n a b q : Nat} (Q : Point) :
    ∀ bits R S ws rest,
      R.canonical n = true → R.onCurve n a b = true →
      replayBits n a b q Q bits R ws = some (S, rest) →
      S.canonical n = true ∧ S.onCurve n a b = true
  | 0, R, S, ws, rest, hcan, hcurve, h => by
      simp only [replayBits, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hcan, hcurve⟩
  | bits + 1, R, S, ws, rest, _, _, h => by
      cases hD : checkedAdd? n a b R R ws with
      | none => simp [replayBits, hD] at h
      | some pair =>
          rcases pair with ⟨D, ws₁⟩
          have hDf := checkedAdd_facts hD
          cases hbit : q.testBit bits with
          | false =>
              have hrec : replayBits n a b q Q bits D ws₁ =
                  some (S, rest) := by
                simpa [replayBits, hD, hbit] using h
              exact replayBits_facts Q bits D S ws₁ rest hDf.2.1 hDf.2.2 hrec
          | true =>
              cases hT : checkedAdd? n a b D Q ws₁ with
              | none => simp [replayBits, hD, hbit, hT] at h
              | some pair =>
                  rcases pair with ⟨T, ws₂⟩
                  have hTf := checkedAdd_facts hT
                  have hrec : replayBits n a b q Q bits T ws₂ =
                      some (S, rest) := by
                    simpa [replayBits, hD, hbit, hT] using h
                  exact replayBits_facts Q bits T S ws₂ rest
                    hTf.2.1 hTf.2.2 hrec

/-- A successful scalar replay returns canonical coordinates satisfying the curve equation. -/
theorem replay_facts {n a b q : Nat} {Q S : Point} {ws rest : List Nat}
    (h : replay n a b q Q ws = some (S, rest)) :
    S.canonical n = true ∧ S.onCurve n a b = true := by
  exact replayBits_facts Q ((Nat.log2 q + 1)) .infinity S ws rest
    (by rfl) (by rfl) h

/-- Scalar acceptance means infinity with no unused inverse witnesses. -/
theorem replayDone_eq_true_iff {n a b q : Nat} {Q : Point}
    {inverses : List Nat} :
    replayDone n a b q Q inverses = true ↔
      replay n a b q Q inverses = some (.infinity, []) := by
  unfold replayDone
  cases h : replay n a b q Q inverses with
  | none => simp
  | some pair =>
    rcases pair with ⟨P, ws⟩
    cases P <;> cases ws <;> simp

/-- The next binary digit extends the truncated scalar by its positional value. -/
theorem bit_mod_succ (q k : Nat) :
    q % 2 ^ (k + 1) =
      q % 2 ^ k + (q.testBit k).toNat * 2 ^ k := by
  rw [Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]

/-- A stronger, elementary size condition: q > 2√n + 1. -/
def sizeBound (n q : Nat) : Bool :=
  4 * n < (q - 1) * (q - 1)
end Hex.ECPP
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





/-!
# Checking elliptic curve primality certificates

The checker verifies the data for the Hasse-bound primality argument: a
nonsingular curve modulo the candidate integer, a finite point annihilated by
a sufficiently large prime, and a certificate for that prime. Divisions are
justified by supplied modular inverses, each checked by multiplication.

`checkAt n cert` also requires that the certificate is for `n`. The theorem
turning acceptance into `Nat.Prime n` is in `HexECPPTheory.Soundness`.
-/

namespace Hex.ECPP

/-- Check the elliptic curve conditions that establish `n` prime once `q` is
known prime: a nonsingular short Weierstrass curve, a finite point `(x,y)`,
verified divisions in `q • (x,y) = O`, and a sufficiently large `q < n`.
This function checks the local arithmetic; it does not itself prove `q`
prime. `check` additionally checks the nested certificate for `q`. -/

def checkStep (n a b x y discrInv : Nat) (inverses : List Nat) (q : Nat) : Bool :=
  3 < n && (n % 6 == 1 || n % 6 == 5) &&
    2 ≤ q && q < n &&
    a < n && b < n && x < n && y < n && discrInv < n &&
    onCurve n a b x y &&
    (4 * a * a * a + 27 * b * b) * discrInv % n == 1 &&
    sizeBound n q && q < 2 ^ (Nat.log2 q + 1) &&
    replayDone n a b q (.affine x y) inverses

/-- Accepted step data uses canonical curve, point and discriminant residues. -/
theorem checkStep_canonical {n a b x y discrInv q : Nat}
    {inverses : List Nat}
    (h : checkStep n a b x y discrInv inverses q = true) :
    a < n ∧ b < n ∧ x < n ∧ y < n ∧ discrInv < n := by
  simp only [checkStep, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_iff, beq_iff_eq] at h
  grind

/-- An accepted step satisfies the curve, inverse and size conditions, and
its scalar multiplication reaches infinity with no unused inverse witnesses. -/
theorem checkStep_facts {n a b x y discrInv q : Nat} {inverses : List Nat}
    (h : checkStep n a b x y discrInv inverses q = true) :
    3 < n ∧ (n % 6 = 1 ∨ n % 6 = 5) ∧ 2 ≤ q ∧ q < n ∧
      onCurve n a b x y = true ∧
      (4 * a * a * a + 27 * b * b) * discrInv % n = 1 ∧
      sizeBound n q = true ∧ q < 2 ^ (Nat.log2 q + 1) ∧
      replay n a b q (.affine x y) inverses = some (.infinity, []) := by
  simp only [checkStep, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_iff, beq_iff_eq] at h
  have hreplay := replayDone_eq_true_iff.mp h.2
  grind

end Hex.ECPP
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/







/-!
# Interpreting certificate arithmetic over finite fields

The integer `n` in a primality certificate need not yet be known prime.
For each prime divisor `p` of `n`, verified modular inverses remain inverses
in `ZMod p`, and the curve remains nonsingular. We interpret the supplied
coordinates as Mathlib elliptic curve points and prove that every accepted
addition agrees with the group law. A finite starting point stays different
from the identity after reduction. These facts justify the point-order
argument used to prove `n` prime.
-/


namespace Hex.ECPP

open WeierstrassCurve

/-- The short Weierstrass curve supplied by an ECPP step, reduced modulo `p`. -/
def shortCurve (p a b : ℕ) : WeierstrassCurve (ZMod p) :=
  ⟨0, 0, 0, a, b⟩

/-- The checker's short curve has zero coefficients `a₁`, `a₂` and `a₃`. -/
instance shortCurveIsShortNF (p a b : ℕ) : (shortCurve p a b).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

/-- The checker coprimality guard excludes characteristics two and three. -/
theorem prime_divisor_gt_three {p n : ℕ} (prime : p.Prime) (hp : p ∣ n)
    (hmod : n % 6 = 1 ∨ n % 6 = 5) : 3 < p := by
  have hp2 := prime.two_le
  by_contra h
  have hsmall : p = 2 ∨ p = 3 := by omega
  rcases hsmall with rfl | rfl
  · obtain ⟨k, rfl⟩ := hp
    rcases hmod with hmod | hmod <;> omega
  · obtain ⟨k, rfl⟩ := hp
    rcases hmod with hmod | hmod <;> omega

/-- Reduction modulo a multiple of `p` preserves the residue in `ZMod p`. -/
theorem cast_mod {p n : ℕ} (hp : p ∣ n) (t : ℕ) :
    ((t % n : ℕ) : ZMod p) = t := by
  exact (ZMod.natCast_eq_natCast_iff _ _ p).mpr
    ((Nat.mod_modEq t n).of_dvd hp)

/-- The checker's natural modular subtraction is field subtraction after
reduction at any prime divisor. -/
theorem cast_modSub {p n : ℕ} (hp : p ∣ n) (hn : 0 < n) (a b : ℕ) :
    ((modSub n a b : ℕ) : ZMod p) = (a : ZMod p) - b := by
  have hle : b % n ≤ a % n + n := by
    have hb := Nat.mod_lt b hn
    omega
  simp only [modSub, cast_mod hp, Nat.cast_sub hle, Nat.cast_add]
  rw [(ZMod.natCast_eq_zero_iff n p).mpr hp]
  ring

/-- A consumed inverse witness is an actual inverse in every prime residue field. -/
theorem inverse_witness {p n d u : ℕ} [Fact p.Prime] (hp : p ∣ n)
    (h : d * u % n = 1) : (u : ZMod p) = (d : ZMod p)⁻¹ := by
  have hdu := congrArg (fun t : ℕ => (t : ZMod p)) h
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_one] at hdu
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hdu)

/-- The coordinates produced by a checked division branch are the field
secant or tangent formulas over every prime divisor. -/
theorem addWithInverse_reduced {p n x₁ y₁ x₂ d v : ℕ} [Fact p.Prime]
    {ws rest : List ℕ} {R : Point} (hp : p ∣ n) (hn : 0 < n)
    (h : addWithInverse n x₁ y₁ x₂ d v ws = some (R, rest)) :
    ∃ X Y : ℕ, R = .affine X Y ∧
      (X : ZMod p) = ((v : ZMod p) / d) ^ 2 - x₁ - x₂ ∧
      (Y : ZMod p) = ((v : ZMod p) / d) * ((x₁ : ZMod p) - X) - y₁ := by
  obtain ⟨u, _, _, hdu, rfl⟩ := addWithInverse_spec h
  let s := v * u % n
  let X := modSub n (modSub n (s * s % n) x₁) x₂
  let Y := modSub n (s * (modSub n x₁ X) % n) y₁
  have hs : (s : ZMod p) = (v : ZMod p) / d := by
    dsimp [s]
    rw [cast_mod hp, Nat.cast_mul, inverse_witness hp hdu, div_eq_mul_inv]
  refine ⟨X, Y, rfl, ?_, ?_⟩
  · dsimp [X]
    rw [cast_modSub hp hn, cast_modSub hp hn, cast_mod hp, Nat.cast_mul, hs]
    ring
  · dsimp [Y]
    rw [cast_modSub hp hn, cast_mod hp, Nat.cast_mul, cast_modSub hp hn, hs]

/-- A checked raw point lies on the reduced short curve. -/
theorem onCurve_reduced {p n a b x y : ℕ} (hp : p ∣ n)
    (h : onCurve n a b x y = true) :
    (shortCurve p a b).toAffine.Equation (x : ZMod p) (y : ZMod p) := by
  have heq : (y * y) % n = (x * x * x + a * x + b) % n := by
    simpa only [onCurve, beq_iff_eq] using h
  have heq' := congrArg (fun t : ℕ => (t : ZMod p)) heq
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_add] at heq'
  rw [WeierstrassCurve.Affine.equation_iff]
  dsimp [shortCurve]
  simp only [zero_mul, add_zero]
  calc
    (y : ZMod p) ^ 2 = y * y := by ring
    _ = x * x * x + (a : ZMod p) * x + b := heq'
    _ = x ^ 3 + (a : ZMod p) * x + b := by ring

set_option linter.style.haveILetI false in
/-- The checked discriminant inverse makes the reduced short curve nonsingular. -/
theorem shortCurve_elliptic {p n a b inv : ℕ} (prime : p.Prime)
    (hp3 : 3 < p) (hp : p ∣ n)
    (h : ((4 * a * a * a + 27 * b * b) * inv) % n = 1) :
    (shortCurve p a b).toAffine.IsElliptic := by
  letI : Fact p.Prime := ⟨prime⟩
  have hcast := congrArg (fun t : ℕ => (t : ZMod p)) h
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
  have hfactor : (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2) * inv = 1 := by
    calc
      _ = (4 * (a : ZMod p) * a * a + 27 * (b : ZMod p) * b) * inv := by ring
      _ = 1 := hcast
  have hD : (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2) ≠ 0 := by
    intro hz
    have hzero : (0 : ZMod p) = 1 := by simpa only [hz, zero_mul] using hfactor
    exact zero_ne_one hzero
  have h16 : (16 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 16 := (ZMod.natCast_eq_zero_iff 16 p).mp hz
    have hpow : p ∣ 2 ^ 4 := by simpa using hdiv
    have h2 : p ∣ 2 := prime.dvd_of_dvd_pow hpow
    have : p ≤ 2 := Nat.le_of_dvd (by omega) h2
    omega
  apply (WeierstrassCurve.isElliptic_iff (shortCurve p a b)).2
  rw [WeierstrassCurve.Δ_of_isShortNF]
  dsimp [shortCurve]
  have hne : (-16 * (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr h16) hD
  exact isUnit_iff_ne_zero.mpr hne

/-- A raw point represents an actual nonsingular affine point after reducing
its coordinates into a prime field. -/
def Point.Rep (p a b : ℕ) (raw : Point)
    (P : (shortCurve p a b).toAffine.Point) : Prop :=
  match raw with
  | .infinity => P = 0
  | .affine x y =>
      ∃ h : (shortCurve p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p),
        P = .some _ _ h

set_option linter.style.haveILetI false in
/-- The checked starting point represents a nonidentity group element over
every prime divisor of the candidate. -/
theorem startingPoint_rep {p n a b x y inv : ℕ} (prime : p.Prime)
    (hp3 : 3 < p) (hp : p ∣ n)
    (hdisc : ((4 * a * a * a + 27 * b * b) * inv) % n = 1)
    (hcurve : onCurve n a b x y = true) :
    ∃ P : (shortCurve p a b).toAffine.Point,
      (Point.affine x y).Rep p a b P ∧ P ≠ 0 := by
  letI : Fact p.Prime := ⟨prime⟩
  letI : (shortCurve p a b).toAffine.IsElliptic :=
    shortCurve_elliptic prime hp3 hp hdisc
  have heq := onCurve_reduced hp hcurve
  have hnon : (shortCurve p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq
  refine ⟨.some _ _ hnon, ⟨hnon, rfl⟩, ?_⟩
  exact WeierstrassCurve.Affine.Point.some_ne_zero hnon

/-- The witness quotient in the distinct-abscissa branch is Mathlib's
secant slope. -/
theorem secant_slope {p n a b x₁ y₁ x₂ y₂ : ℕ} [Fact p.Prime]
    (hp : p ∣ n) (hn : 0 < n) (hne : (x₁ : ZMod p) ≠ x₂) :
    (shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂ =
      ((modSub n y₂ y₁ : ℕ) : ZMod p) /
        ((modSub n x₂ x₁ : ℕ) : ZMod p) := by
  rw [WeierstrassCurve.Affine.slope, ite_eq_right hne,
    cast_modSub hp hn, cast_modSub hp hn]
  have hy : (y₁ : ZMod p) - y₂ = -((y₂ : ZMod p) - y₁) := by ring
  have hx : (x₁ : ZMod p) - x₂ = -((x₂ : ZMod p) - x₁) := by ring
  rw [hy, hx]
  simp only [div_neg, neg_div, neg_neg]

/-- The witness quotient in the equal-point branch is Mathlib's tangent
slope. The inverse witness excludes a vertical tangent in every field. -/
theorem tangent_slope {p n a b x y u : ℕ} [Fact p.Prime]
    (hp : p ∣ n)
    (hu : (2 * y % n) * u % n = 1) :
    (shortCurve p a b).toAffine.slope x x y y =
      (((3 * x * x + a) % n : ℕ) : ZMod p) /
        (((2 * y) % n : ℕ) : ZMod p) := by
  have hdu := congrArg (fun t : ℕ => (t : ZMod p)) hu
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_one] at hdu
  have h2y : (2 : ZMod p) * y ≠ 0 := by
    intro hz
    simp [hz] at hdu
  have hne : (y : ZMod p) ≠ (shortCurve p a b).toAffine.negY x y := by
    intro hy
    simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul,
      sub_zero] at hy
    apply h2y
    have hsum : (y : ZMod p) + y = 0 := by
      nth_rw 1 [hy]
      exact neg_add_cancel _
    simpa only [two_mul] using hsum
  rw [WeierstrassCurve.Affine.slope, ite_eq_left rfl, ite_eq_right hne,
    cast_mod hp, cast_mod hp]
  simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul,
    sub_zero, Nat.cast_add, Nat.cast_mul]
  congr 1 <;> ring

/-- If raw coordinates equal Mathlib's affine addition formulas, they
represent the actual group sum. -/
theorem formula_rep {p a b x₁ y₁ x₂ y₂ X Y : ℕ} [Fact p.Prime]
    (h₁ : (shortCurve p a b).toAffine.Nonsingular (x₁ : ZMod p) (y₁ : ZMod p))
    (h₂ : (shortCurve p a b).toAffine.Nonsingular (x₂ : ZMod p) (y₂ : ZMod p))
    (hxy : ¬((x₁ : ZMod p) = x₂ ∧
      (y₁ : ZMod p) = (shortCurve p a b).toAffine.negY x₂ y₂))
    (hx : (X : ZMod p) = (shortCurve p a b).toAffine.addX x₁ x₂
      ((shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂))
    (hy : (Y : ZMod p) = (shortCurve p a b).toAffine.addY x₁ x₂ y₁
      ((shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂)) :
    (Point.affine X Y).Rep p a b
      (.some _ _ h₁ + .some _ _ h₂) := by
  have hsum := (shortCurve p a b).toAffine.nonsingular_add h₁ h₂ hxy
  have hXY : (shortCurve p a b).toAffine.Nonsingular (X : ZMod p) (Y : ZMod p) := by
    rw [hx, hy]
    exact hsum
  refine ⟨hXY, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_some hxy]
  simp only [← hx, ← hy]

/-- A checked secant branch is the actual affine group sum in every prime
residue field. -/
theorem secant_rep {p n a b x₁ y₁ x₂ y₂ : ℕ} [Fact p.Prime]
    {ws rest : List ℕ} {R : Point} (hp : p ∣ n) (hn : 0 < n)
    (h₁ : (shortCurve p a b).toAffine.Nonsingular (x₁ : ZMod p) (y₁ : ZMod p))
    (h₂ : (shortCurve p a b).toAffine.Nonsingular (x₂ : ZMod p) (y₂ : ZMod p))
    (h : addWithInverse n x₁ y₁ x₂ (modSub n x₂ x₁)
      (modSub n y₂ y₁) ws = some (R, rest)) :
    R.Rep p a b (.some _ _ h₁ + .some _ _ h₂) := by
  obtain ⟨u, _, _, hdu, _⟩ := addWithInverse_spec h
  have hduF := congrArg (fun t : ℕ => (t : ZMod p)) hdu
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_one,
    cast_modSub hp hn] at hduF
  have hneq : (x₁ : ZMod p) ≠ x₂ := by
    intro heq
    have hz : (x₂ : ZMod p) - x₁ = 0 := sub_eq_zero.mpr heq.symm
    rw [hz] at hduF
    simp at hduF
  obtain ⟨X, Y, rfl, hx, hy⟩ := addWithInverse_reduced hp hn h
  have hslope := secant_slope (a := a) (b := b)
    (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂) hp hn hneq
  have hxF : (X : ZMod p) = (shortCurve p a b).toAffine.addX x₁ x₂
      ((shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [hslope]
    simpa only [WeierstrassCurve.Affine.addX, shortCurve,
      zero_mul, add_zero, zero_sub, sub_zero] using hx
  have hyF : (Y : ZMod p) = (shortCurve p a b).toAffine.addY x₁ x₂ y₁
      ((shortCurve p a b).toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    have hxF' := hxF
    rw [hslope] at hxF'
    rw [← hxF']
    dsimp [shortCurve]
    simp only [zero_mul, sub_zero]
    ring_nf at hy ⊢
    exact hy
  exact formula_rep h₁ h₂ (fun hxy => hneq hxy.1) hxF hyF

/-- A checked tangent branch is the actual affine group sum in every prime
residue field. -/
theorem tangent_rep {p n a b x y : ℕ} [Fact p.Prime]
    {ws rest : List ℕ} {R : Point} (hp : p ∣ n) (hn : 0 < n)
    (hpoint : (shortCurve p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p))
    (h : addWithInverse n x y x (2 * y % n)
      ((3 * x * x + a) % n) ws = some (R, rest)) :
    R.Rep p a b (.some _ _ hpoint + .some _ _ hpoint) := by
  obtain ⟨u, _, _, hdu, _⟩ := addWithInverse_spec h
  have hduF := congrArg (fun t : ℕ => (t : ZMod p)) hdu
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_one] at hduF
  have hne : (y : ZMod p) ≠ (shortCurve p a b).toAffine.negY x y := by
    intro heq
    simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul,
      sub_zero] at heq
    have hz : (2 : ZMod p) * y = 0 := by
      have hsum : (y : ZMod p) + y = 0 := by
        nth_rw 1 [heq]
        exact neg_add_cancel _
      simpa only [two_mul] using hsum
    norm_num only [Nat.cast_ofNat] at hduF
    rw [hz] at hduF
    simp at hduF
  obtain ⟨X, Y, rfl, hx, hy⟩ := addWithInverse_reduced hp hn h
  have hslope := tangent_slope (a := a) (b := b) (x := x) (y := y) hp hdu
  have hxF : (X : ZMod p) = (shortCurve p a b).toAffine.addX x x
      ((shortCurve p a b).toAffine.slope x x y y) := by
    rw [hslope]
    simpa only [WeierstrassCurve.Affine.addX, shortCurve,
      zero_mul, add_zero, zero_sub, sub_zero] using hx
  have hyF : (Y : ZMod p) = (shortCurve p a b).toAffine.addY x x y
      ((shortCurve p a b).toAffine.slope x x y y) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    have hxF' := hxF
    rw [hslope] at hxF'
    rw [← hxF']
    dsimp [shortCurve]
    simp only [zero_mul, sub_zero]
    ring_nf at hy ⊢
    exact hy
  exact formula_rep hpoint hpoint (fun hxy => hne hxy.2) hxF hyF

/-- Every accepted raw addition agrees with Mathlib's group law after
reduction to a prime divisor. -/
theorem add_rep {p n a b : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    {P Q R : Point} {U V : (shortCurve p a b).toAffine.Point}
    {ws rest : List ℕ} (hP : P.Rep p a b U) (hQ : Q.Rep p a b V)
    (h : add? n a P Q ws = some (R, rest)) :
    R.Rep p a b (U + V) := by
  cases P with
  | infinity =>
    simp only [Point.Rep] at hP
    simp only [add?] at h
    cases h
    simpa [hP] using hQ
  | affine x₁ y₁ =>
    cases Q with
    | infinity =>
      simp only [Point.Rep] at hQ
      simp only [add?] at h
      cases h
      simpa [hQ] using hP
    | affine x₂ y₂ =>
      obtain ⟨h₁, rfl⟩ := hP
      obtain ⟨h₂, rfl⟩ := hQ
      by_cases hx : x₁ = x₂
      · subst x₂
        by_cases hzero : (y₁ + y₂) % n = 0
        · have hfield := congrArg (fun t : ℕ => (t : ZMod p)) hzero
          simp only [cast_mod hp, Nat.cast_add, Nat.cast_zero] at hfield
          have hy : (y₁ : ZMod p) =
              (shortCurve p a b).toAffine.negY x₁ y₂ := by
            simp only [WeierstrassCurve.Affine.negY, shortCurve,
              zero_mul, sub_zero]
            exact eq_neg_of_add_eq_zero_left hfield
          have hgroup := WeierstrassCurve.Affine.Point.add_of_Y_eq
            (h₁ := h₁) (h₂ := h₂) rfl hy
          simp [add?, hzero] at h
          rcases h with ⟨rfl, rfl⟩
          simp [Point.Rep, hgroup]
        · by_cases hy : y₁ = y₂
          · subst y₂
            have h' : addWithInverse n x₁ y₁ x₁ (2 * y₁ % n)
                ((3 * x₁ * x₁ + a) % n) ws = some (R, rest) := by
              simpa [add?, hzero] using h
            exact tangent_rep hp hn h₁ h'
          · simp [add?, hzero, hy] at h
      · have h' : addWithInverse n x₁ y₁ x₂ (modSub n x₂ x₁)
            (modSub n y₂ y₁) ws = some (R, rest) := by
          simpa [add?, hx] using h
        exact secant_rep hp hn h₁ h₂ h'

end Hex.ECPP
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





/-!
# Point orders exclude small prime divisors

If a nonidentity point in a finite group satisfies `q • Q = 0` for a prime
`q`, its order is exactly `q`. Lagrange's theorem then makes `q` a divisor
of the group size. For an elliptic curve reduced modulo a prime divisor
`p` of the candidate `n`, this gives `q ≤ #E(𝔽_p)`.

Hasse's bound and the certificate's strict size condition together rule out
`p² ≤ n`. This is the contradiction needed to prove `n` prime.
-/


namespace Hex.ECPP

set_option linter.style.haveILetI false in
/-- A nonzero point annihilated by a prime has that order, which divides the
cardinality of its finite group. -/
theorem prime_order_dvd_card {G : Type*} [AddGroup G] [Fintype G]
    {q : ℕ} (hq : q.Prime) {Q : G} (hne : Q ≠ 0) (hzero : q • Q = 0) :
    q ∣ Fintype.card G := by
  letI : Fact q.Prime := ⟨hq⟩
  have hord : addOrderOf Q = q := addOrderOf_eq_prime hzero hne
  rw [← hord]
  exact addOrderOf_dvd_card

/-- A prime annihilating a nonzero point is at most the finite group order. -/
theorem prime_order_le_card {G : Type*} [AddGroup G] [Fintype G]
    {q : ℕ} (hq : q.Prime) {Q : G} (hne : Q ≠ 0) (hzero : q • Q = 0) :
    q ≤ Fintype.card G := by
  exact Nat.le_of_dvd Fintype.card_pos (prime_order_dvd_card hq hne hzero)


open WeierstrassCurve
noncomputable instance pointFintype {F : Type*} [CommRing F] [Fintype F]
    (W : WeierstrassCurve.Affine F) : Fintype W.Point := by
  classical
  letI : Fintype (WithZero {xy : F × F // W.Nonsingular xy.fst xy.snd}) :=
    Fintype.ofEquiv (Option {xy : F × F // W.Nonsingular xy.fst xy.snd}) (Equiv.refl _)
  exact Fintype.ofEquiv (WithZero {xy : F × F // W.Nonsingular xy.fst xy.snd})
    (W.nonsingularPointEquiv).symm

def pointCode {p a b : ℕ} [Fact p.Prime] :
    (shortCurve p a b).toAffine.Point → Option (ZMod p × Bool)
  | .zero => none
  | .some x y _ => some (x, decide (y.val ≤ (-y).val))

theorem card_bound (p a b : ℕ) [Fact p.Prime] :
    Fintype.card (shortCurve p a b).toAffine.Point ≤ 2*p+1 := by
  classical
  have hinj : Function.Injective (@pointCode p a b _) := by
    intro P Q h
    cases P with
    | zero => cases Q <;> simp [pointCode] at h ⊢
    | some x y hy =>
      cases Q with
      | zero => simp [pointCode] at h
      | some X Y hY =>
        simp only [pointCode, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, hb⟩ := h
        have e1 := hy.1
        have e2 := hY.1
        rw [WeierstrassCurve.Affine.equation_iff] at e1 e2
        simp [shortCurve] at e1 e2
        have hs : y ^ 2 = Y ^ 2 := e1.trans e2.symm
        have hor : y = Y ∨ y = -Y := by
          have hh : (y-Y)*(y+Y) = 0 := by linear_combination hs
          rcases mul_eq_zero.mp hh with hh | hh
          · exact Or.inl (sub_eq_zero.mp hh)
          · exact Or.inr (eq_neg_of_add_eq_zero_left hh)
        rcases hor with he | he
        · subst Y
          rfl
        · subst y
          by_cases hv : Y.val = (-Y).val
          · have heq : Y = -Y := ZMod.val_injective p hv
            congr 1
            exact heq.symm
          · simp only [neg_neg] at hb
            by_cases hl : Y.val ≤ (-Y).val
            · have hn : ¬ (-Y).val ≤ Y.val := by omega
              simp [hl, hn] at hb
            · have hn : (-Y).val ≤ Y.val := by omega
              simp [hl, hn] at hb
  have hc := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_option, Fintype.card_prod, ZMod.card, Fintype.card_bool,
    Nat.mul_comm, Nat.add_comm] using hc

end Hex.ECPP
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





/-!
# Why accepted elliptic curve certificates prove primality

For every prime divisor `p` of the candidate integer `n`, an accepted
certificate gives a nonidentity point on an elliptic curve over `ZMod p`
annihilated by the auxiliary prime `q`. Its order is exactly `q`, so Hasse's
bound excludes `p ≤ √n` once the certificate's size inequality holds.
This rules out compositeness. Recursion checks the primality certificate
for `q` and ultimately reduces to HexPrimality's existing soundness theorem.

`natPrime_of_checkAt` has just the checker equation as its premise. Curve
orders proposed during search, random choices, and external programs are not
assumptions of the resulting `Nat.Prime n` theorem.
-/


namespace Hex.ECPP

/-- The structurally recursive raw replay computes the canonical binary
prefix of the scalar in the actual elliptic-curve group. -/
theorem replayBits_rep {p n a b q : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    (Q : Point) (V : (shortCurve p a b).toAffine.Point)
    (hQ : Q.Rep p a b V) :
    ∀ (k : ℕ) {R S : Point} {ws rest : List ℕ}
      (U : (shortCurve p a b).toAffine.Point),
      R.Rep p a b U → replayBits n a b q Q k R ws = some (S, rest) →
      S.Rep p a b ((2 ^ k) • U + (q % 2 ^ k) • V)
  | 0, R, S, ws, rest, U, hR, h => by
      simp only [replayBits, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [Nat.mod_one] using hR
  | k + 1, R, S, ws, rest, U, hR, h => by
      cases hD : checkedAdd? n a b R R ws with
      | none => simp [replayBits, hD] at h
      | some pair =>
        rcases pair with ⟨D, ws₁⟩
        have hDrep := add_rep hp hn hR hR (checkedAdd_facts hD).1
        cases hbit : q.testBit k with
        | false =>
          have hrec : replayBits n a b q Q k D ws₁ = some (S, rest) := by
            simpa [replayBits, hD, hbit] using h
          have hrecRep := replayBits_rep hp hn Q V hQ k (U + U) hDrep hrec
          have hscalar : (2 ^ k) • (U + U) + (q % 2 ^ k) • V =
              (2 ^ (k + 1)) • U + (q % 2 ^ (k + 1)) • V := by
            rw [bit_mod_succ]
            simp [hbit, pow_succ, mul_nsmul, nsmul_add, two_nsmul]
          rw [← hscalar]
          exact hrecRep
        | true =>
          cases hT : checkedAdd? n a b D Q ws₁ with
          | none => simp [replayBits, hD, hbit, hT] at h
          | some pair =>
            rcases pair with ⟨T, ws₂⟩
            have hrec : replayBits n a b q Q k T ws₂ = some (S, rest) := by
              simpa [replayBits, hD, hbit, hT] using h
            have hTrep := add_rep hp hn hDrep hQ (checkedAdd_facts hT).1
            have hrecRep := replayBits_rep hp hn Q V hQ k
              ((U + U) + V) hTrep hrec
            have hscalar : (2 ^ k) • ((U + U) + V) + (q % 2 ^ k) • V =
                (2 ^ (k + 1)) • U + (q % 2 ^ (k + 1)) • V := by
              rw [bit_mod_succ]
              simp [hbit, pow_succ, mul_nsmul, nsmul_add, add_nsmul, two_nsmul]
              abel
            rw [← hscalar]
            exact hrecRep

/-- If the complete replay returns infinity, its field point is annihilated
by the child subject. -/
theorem replay_zero {p n a b q : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    (Q : Point) (V : (shortCurve p a b).toAffine.Point)
    (hQ : Q.Rep p a b V) {ws rest : List ℕ}
    (hbits : q < 2 ^ (Nat.log2 q + 1))
    (h : replay n a b q Q ws = some (.infinity, rest)) : q • V = 0 := by
  have hrep := replayBits_rep hp hn Q V hQ ((Nat.log2 q + 1))
    (R := .infinity) (S := .infinity) (ws := ws) (rest := rest)
    0 (by rfl) h
  change (2 ^ (Nat.log2 q + 1)) • (0 : (shortCurve p a b).toAffine.Point) +
    (q % 2 ^ (Nat.log2 q + 1)) • V = 0 at hrep
  simpa [Nat.mod_eq_of_lt (hbits)] using hrep

set_option linter.style.haveILetI false in
/-- A checked ECPP step is prime once its structurally smaller child subject
is prime. No primality of the candidate is assumed. -/
theorem natPrime_of_step {n a b x y discrInv q : ℕ} {inverses : List ℕ}
    (hq : q.Prime)
    (h : checkStep n a b x y discrInv inverses q = true) : n.Prime := by
  obtain ⟨hn3, hmod, _, _, hcurve, hdisc, hsize, hbits, hreplay⟩ := checkStep_facts h
  by_contra hnp
  let p := Nat.minFac n
  have hpPrime : p.Prime := Nat.minFac_prime (by omega : n ≠ 1)
  have hpDiv : p ∣ n := Nat.minFac_dvd n
  have hpSq : p * p ≤ n := by
    simpa only [pow_two] using Nat.minFac_sq_le_self (by omega : 0 < n) hnp
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hp3 : 3 < p := prime_divisor_gt_three hpPrime hpDiv hmod
  letI : (shortCurve p a b).toAffine.IsElliptic :=
    shortCurve_elliptic hpPrime hp3 hpDiv hdisc
  obtain ⟨P, hP, hP0⟩ := startingPoint_rep hpPrime hp3 hpDiv hdisc hcurve
  have hzero : q • P = 0 := replay_zero hpDiv (by omega) _ P hP hbits hreplay
  have horder : q ≤ Fintype.card (shortCurve p a b).toAffine.Point :=
    prime_order_le_card hq hP0 hzero
  have hle : q ≤ 2*p+1 := horder.trans (card_bound p a b)
  have hqle : q - 1 ≤ 2*p := by omega
  have hsq := Nat.mul_le_mul hqle hqle
  have hh : 4*n < (q-1)*(q-1) := of_decide_eq_true hsize
  nlinarith [hsq, hpSq]

end Hex.ECPP

/- Division-free certificate replay. All additions are justified by a product
of non-equivalence witnesses, inverted only once per certificate row. -/
namespace Hex.ECPP
open WeierstrassCurve
open scoped WeierstrassCurve.Jacobian
namespace JacobianReplay

structure Raw where
  X : ℕ
  Y : ℕ
  Z : ℕ
deriving DecidableEq

def infinity : Raw := ⟨1, 1, 0⟩
def liftPoint (x y : ℕ) : Raw := ⟨x,y,1⟩

def dbl (n a : ℕ) (P : Raw) : Raw :=
  let v := 2 * P.Y % n
  let u := (3 * P.X ^ 2 + a * P.Z ^ 4) % n
  let X := modSub n (u ^ 2) (2 * P.X * v ^ 2)
  let Y := modSub n (u * modSub n (P.X * v ^ 2) X) (P.Y * v ^ 3)
  ⟨X,Y,P.Z * v % n⟩

def mixed (n a b : ℕ) (P : Raw) (x y : ℕ) : Raw :=
  let X := modSub n (P.X*x^2*P.Z^2 + P.X^2*x + a*x*P.Z^4 + a*P.X*P.Z^2 + 2*b*P.Z^4)
      (2*P.Y*y*P.Z)
  let Y := modSub n (P.Y*x^3*P.Z^3 + 3*P.X^2*x*y*P.Z^2 + 2*P.Y^2*y + a*x*y*P.Z^6 +
      a*P.X*y*P.Z^4 + 2*b*y*P.Z^6)
      (2*P.Y*y^2*P.Z^3 + 3*P.X*P.Y*x^2*P.Z + P.X^3*y + a*P.Y*x*P.Z^3 +
        a*P.X*P.Y*P.Z + 2*b*P.Y*P.Z^3)
  ⟨X,Y,modSub n P.X (x*P.Z^2)⟩

def guard (n : ℕ) (P : Raw) (x y : ℕ) : ℕ :=
  let d := modSub n P.X (x*P.Z^2)
  if d = 0 then modSub n P.Y (y*P.Z^3) else d

def replay (n a b x y q : ℕ) : ℕ → Raw × ℕ → Raw × ℕ
  | 0, S => S
  | k+1, S =>
    let D := dbl n a S.1
    if q.testBit k then
      replay n a b x y q k (mixed n a b D x y, S.2 * guard n D x y % n)
    else replay n a b x y q k (D,S.2)

def fieldPoint (p : ℕ) (P : Raw) : Fin 3 → ZMod p :=
  ![(P.X : ZMod p), (P.Y : ZMod p), (P.Z : ZMod p)]

theorem dbl_cast {p n a b : ℕ} (hp : p ∣ n) (hn : 0 < n) (P : Raw) :
    fieldPoint p (dbl n a P) =
      (shortCurve p a b).toJacobian.dblXYZ (fieldPoint p P) := by
  ext i
  fin_cases i <;>
    simp [fieldPoint, dbl, cast_mod hp, cast_modSub hp hn, shortCurve,
      WeierstrassCurve.Jacobian.dblXYZ, WeierstrassCurve.Jacobian.dblX,
      WeierstrassCurve.Jacobian.dblY, WeierstrassCurve.Jacobian.dblZ,
      WeierstrassCurve.Jacobian.dblU_eq, WeierstrassCurve.Jacobian.negDblY,
      WeierstrassCurve.Jacobian.negY] <;> ring

theorem mixed_cast {p n a b : ℕ} (hp : p ∣ n) (hn : 0 < n) (P : Raw) (x y : ℕ) :
    fieldPoint p (mixed n a b P x y) =
      (shortCurve p a b).toJacobian.addXYZ (fieldPoint p P) (fieldPoint p (liftPoint x y)) := by
  ext i
  fin_cases i <;>
    simp [fieldPoint, liftPoint, mixed, cast_mod hp, cast_modSub hp hn, shortCurve,
      WeierstrassCurve.Jacobian.addXYZ, WeierstrassCurve.Jacobian.addX,
      WeierstrassCurve.Jacobian.addY, WeierstrassCurve.Jacobian.addZ,
      WeierstrassCurve.Jacobian.negAddY, WeierstrassCurve.Jacobian.negY] <;> ring

theorem guard_not_equiv {p n : ℕ} (hp : p ∣ n) (hn : 0 < n)
    (P : Raw) (x y : ℕ) (hg : (guard n P x y : ZMod p) ≠ 0) :
    ¬ fieldPoint p P ≈ fieldPoint p (liftPoint x y) := by
  unfold guard at hg
  split at hg
  · apply WeierstrassCurve.Jacobian.not_equiv_of_Y_ne
    simpa [fieldPoint, liftPoint, cast_modSub hp hn, sub_ne_zero] using hg
  · apply WeierstrassCurve.Jacobian.not_equiv_of_X_ne
    simpa [fieldPoint, liftPoint, cast_modSub hp hn, sub_ne_zero] using hg

/-- The final guard can be nonzero only if every guard used along the way is nonzero. -/
theorem guard_initial_nonzero {p n : ℕ} [Fact p.Prime] (hp : p ∣ n)
    (a b x y q : ℕ) :
    ∀ (k : ℕ) (S : Raw × ℕ),
      ((replay n a b x y q k S).2 : ZMod p) ≠ 0 → (S.2 : ZMod p) ≠ 0
  | 0, S, h => h
  | k+1, S, h => by
    rw [replay] at h
    split at h
    · have hh := guard_initial_nonzero hp a b x y q k _ h
      simp only [cast_mod hp, Nat.cast_mul, mul_ne_zero_iff] at hh
      exact hh.1
    · exact guard_initial_nonzero hp a b x y q k _ h

/-- Field interpretation of the complete division-free scalar replay. -/
theorem replay_rep {p n a b x y q : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    (hQ : (shortCurve p a b).toJacobian.Nonsingular (fieldPoint p (liftPoint x y))) :
    ∀ (k : ℕ) (S : Raw × ℕ),
      (shortCurve p a b).toJacobian.Nonsingular (fieldPoint p S.1) →
      ((replay n a b x y q k S).2 : ZMod p) ≠ 0 →
      (shortCurve p a b).toJacobian.Nonsingular (fieldPoint p (replay n a b x y q k S).1) ∧
      WeierstrassCurve.Jacobian.Point.toAffine (shortCurve p a b).toJacobian
          (fieldPoint p (replay n a b x y q k S).1) =
        (2^k) • WeierstrassCurve.Jacobian.Point.toAffine (shortCurve p a b).toJacobian (fieldPoint p S.1) +
        (q % 2^k) • WeierstrassCurve.Jacobian.Point.toAffine (shortCurve p a b).toJacobian (fieldPoint p (liftPoint x y))
  | 0, S, hS, _ => by simp [replay, hS]
  | k+1, S, hS, hg => by
    let W := (shortCurve p a b).toJacobian
    let D := dbl n a S.1
    have hDcast : fieldPoint p D = W.add (fieldPoint p S.1) (fieldPoint p S.1) := by
      rw [WeierstrassCurve.Jacobian.add_self]
      exact dbl_cast hp hn S.1
    have hD : W.Nonsingular (fieldPoint p D) := by
      rw [hDcast]
      exact WeierstrassCurve.Jacobian.nonsingular_add hS hS
    have hDaff : WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p D) =
        WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p S.1) +
        WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p S.1) := by
      rw [hDcast, WeierstrassCurve.Jacobian.Point.toAffine_add hS hS]
    cases hb : q.testBit k with
    | false =>
      have hgf : ((replay n a b x y q k (D,S.2)).2 : ZMod p) ≠ 0 := by
        simpa [replay,hb,D] using hg
      have hr := replay_rep hp hn hQ k (D,S.2) hD hgf
      simp only [replay, hb, Bool.false_eq_true, if_false]
      refine ⟨hr.1, ?_⟩
      rw [hr.2, hDaff, bit_mod_succ]
      simp [hb, pow_succ, mul_nsmul, nsmul_add, two_nsmul]
    | true =>
      let M := mixed n a b D x y
      let g := S.2 * guard n D x y % n
      have hgf : ((replay n a b x y q k (M,g)).2 : ZMod p) ≠ 0 := by
        simpa [replay,hb,D,M,g] using hg
      have hgi := guard_initial_nonzero hp a b x y q k (M,g) hgf
      have hguard : (guard n D x y : ZMod p) ≠ 0 := by
        change ((S.2 * guard n D x y % n : ℕ) : ZMod p) ≠ 0 at hgi
        simp only [cast_mod hp, Nat.cast_mul, mul_ne_zero_iff] at hgi
        exact hgi.2
      have hMcast : fieldPoint p M =
          W.add (fieldPoint p D) (fieldPoint p (liftPoint x y)) := by
        rw [WeierstrassCurve.Jacobian.add_of_not_equiv (guard_not_equiv hp hn D x y hguard)]
        exact mixed_cast hp hn D x y
      have hM : W.Nonsingular (fieldPoint p M) := by
        rw [hMcast]
        exact WeierstrassCurve.Jacobian.nonsingular_add hD hQ
      have hMaff : WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p M) =
          WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p D) +
          WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p (liftPoint x y)) := by
        rw [hMcast, WeierstrassCurve.Jacobian.Point.toAffine_add hD hQ]
      have hr := replay_rep hp hn hQ k (M,g) hM hgf
      simp only [replay, hb, if_pos rfl]
      refine ⟨hr.1, ?_⟩
      rw [hr.2, hMaff, hDaff, bit_mod_succ]
      simp [hb, pow_succ, mul_nsmul, nsmul_add, add_nsmul, two_nsmul]
      abel
end JacobianReplay
end Hex.ECPP

namespace Hex.ECPP.JacobianReplay
open WeierstrassCurve
open scoped WeierstrassCurve.Jacobian

def check (n a b x y discrInv guardInv q : ℕ) : Bool :=
  let R := replay n a b x y q (q.log2+1) (infinity,1)
  3 < n && (n % 6 == 1 || n % 6 == 5) &&
    2 ≤ q && q < n &&
    onCurve n a b x y &&
    (4*a*a*a+27*b*b)*discrInv % n == 1 &&
    sizeBound n q && q < 2^(q.log2+1) &&
    R.1.Z == 0 && R.2*guardInv % n == 1

theorem prime_of_check {n a b x y discrInv guardInv q : ℕ}
    (hq : q.Prime) (hc : check n a b x y discrInv guardInv q = true) :
    n.Prime := by
  let R := replay n a b x y q (q.log2+1) (infinity,1)
  have h : 3 < n ∧ (n % 6 = 1 ∨ n % 6 = 5) ∧
      2 ≤ q ∧ q < n ∧ onCurve n a b x y = true ∧
      (4*a*a*a+27*b*b)*discrInv % n = 1 ∧
      sizeBound n q = true ∧ q < 2^(q.log2+1) ∧
      R.1.Z = 0 ∧ R.2*guardInv % n = 1 := by
    simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff, beq_iff_eq] at hc
    dsimp [R]
    grind
  obtain ⟨hn3,hmod,_,_,hcurve,hdisc,hsize,hbits,hz,hguard⟩ := h
  by_contra hnp
  let p := Nat.minFac n
  have hpPrime : p.Prime := Nat.minFac_prime (by omega : n ≠ 1)
  have hpDiv : p ∣ n := Nat.minFac_dvd n
  have hpSq : p*p ≤ n := by
    simpa only [pow_two] using Nat.minFac_sq_le_self (by omega : 0 < n) hnp
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hp3 : 3 < p := prime_divisor_gt_three hpPrime hpDiv hmod
  let W := (shortCurve p a b).toJacobian
  letI : (shortCurve p a b).toAffine.IsElliptic :=
    shortCurve_elliptic hpPrime hp3 hpDiv hdisc
  have hQaff : (shortCurve p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p) :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp (onCurve_reduced hpDiv hcurve)
  have hQ : W.Nonsingular (fieldPoint p (liftPoint x y)) := by
    simpa [fieldPoint, liftPoint, W, WeierstrassCurve.Jacobian.nonsingular_some] using hQaff
  have hO : W.Nonsingular (fieldPoint p infinity) := by
    simpa [fieldPoint,infinity,W] using
      (WeierstrassCurve.Jacobian.nonsingular_zero (W' := (shortCurve p a b).toJacobian))
  have hgi : (R.2 : ZMod p) ≠ 0 := by
    have hh := congrArg (fun t : ℕ => (t : ZMod p)) hguard
    simp only [cast_mod hpDiv, Nat.cast_mul, Nat.cast_one] at hh
    intro he
    rw [he, zero_mul] at hh
    exact zero_ne_one hh
  have hR := replay_rep hpDiv (by omega : 0 < n) hQ (q.log2+1) (infinity,1) hO hgi
  have hRzero : WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p R.1) = 0 := by
    apply WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero
    simp [fieldPoint,hz]
  have hOzero : WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p infinity) = 0 := by
    apply WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero
    simp [fieldPoint,infinity]
  let Q := WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p (liftPoint x y))
  have hQ0 : Q ≠ 0 := by
    dsimp [Q,fieldPoint,liftPoint]
    rw [WeierstrassCurve.Jacobian.Point.toAffine_some (by simpa [fieldPoint,liftPoint] using hQ)]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  -- The first projection is nonsingularity; only the second is needed here.
  have hEq := hR.2
  change WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p R.1) =
    (2^(q.log2+1)) • WeierstrassCurve.Jacobian.Point.toAffine W (fieldPoint p infinity) +
      (q % 2^(q.log2+1)) • Q at hEq
  rw [hRzero,hOzero,Nat.mod_eq_of_lt hbits,nsmul_zero,zero_add] at hEq
  have horder : q ≤ Fintype.card (shortCurve p a b).toAffine.Point :=
    prime_order_le_card hq hQ0 hEq.symm
  have hle : q ≤ 2*p+1 := horder.trans (card_bound p a b)
  have hqle : q - 1 ≤ 2*p := by omega
  have hsq := Nat.mul_le_mul hqle hqle
  have hh : 4*n < (q-1)*(q-1) := of_decide_eq_true hsize
  nlinarith [hsq,hpSq]

end Hex.ECPP.JacobianReplay

#print axioms Hex.ECPP.JacobianReplay.prime_of_check

set_option maxRecDepth 200000
set_option maxHeartbeats 50000000
set_option exponentiation.threshold 2000

theorem largestJacobianRow : Hex.ECPP.JacobianReplay.check 9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999997793 1105266768478904207204981280965949346564587965060668597758396371313500666713359038842134472811016360921354542357567986124304106269675182219698035849833407388986516227284144574927442664533589782863064448213080945645648885989196868415976958402795025435321790455009725767441215560658916063921794778377272314140680641952 6236831463752588823176950055437724355689102035841031356539460265358003123276412544783515829861328399410142465358869315086405609691374052716305516046539964104731087095322032524873089676479984562118161338933360883489879632105897770768247827501588491200216051870167583206894935408247971578217850896263728388574342448315 4890104778155375379268044005869619571513309421385795636894260084425695564473805935716880815678636798083869343750424494700707016621906562426369573435315465897182383914917857963728712681915504608336240621724482203660916132937684188800442972265816529825346392902090175983725371523411178730698925549359082470842445521405 5480898357851251378413511266288060096927262193002480751518949639833774494365810409814313969140650726838449819177600394676579982919086714159639706961588840419100286448961167600423262116776890350967141370053172853778984339763941829946852106619931383352302207237932824712205892404164931845643102743923873565489684010225 2290895026137120378583130431077944454794571663161714552158256172355641238633597272666183781720930023768175517577116458817249684423248648999941203905571457491324176099072224896748219821080368261128173824420202689228345440486147783840958886173774619832758803569058623795537265631252859837678073833739677186438636070463 6538612381525547257302351424893144483101037482271581679313640064332829264987082397646741980359292163829941587695686950065702365652215633504143166809028095764168254274368341751736203972617727695758984023980556238482150839593270872868692550343644502424979281486766746022565357728332085548408375458764905519266210948245 19911083527150487808106035584454176317644082987101524182097075089389190524940522408328369654653652608986722930204611590593572300637252626638892438313194384831058728760389162623063843991495986189046678065967808876509929271282353118197287487284561316865241583054243447324368133865979947697586877876155639877 = true := by decide +kernel
#print axioms largestJacobianRow
