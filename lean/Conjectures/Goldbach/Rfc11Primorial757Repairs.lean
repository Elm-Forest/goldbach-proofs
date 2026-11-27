import Mathlib

/- Third-party license for the adapted ECPP checker:
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for describing the origin of the Work and
      reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may accept and charge a
      fee for acceptance of support, warranty, indemnity, or other liability
      obligations and/or rights consistent with this License. However, in
      accepting such obligations, You may act only on Your own behalf
      and on Your sole responsibility, not on behalf of any other Contributor,
      and only if You agree to indemnify, defend, and hold each Contributor
      harmless for any liability incurred by, or claims asserted against,
      such Contributor by reason of your accepting any such warranty or
      additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing permissions and
   limitations under the License.

-/
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

namespace GoldbachRfc11PrimorialECPP

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
  | .affine x y => GoldbachRfc11PrimorialECPP.onCurve n a b x y

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

end GoldbachRfc11PrimorialECPP
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

namespace GoldbachRfc11PrimorialECPP

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
end GoldbachRfc11PrimorialECPP
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

namespace GoldbachRfc11PrimorialECPP

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

end GoldbachRfc11PrimorialECPP
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


namespace GoldbachRfc11PrimorialECPP

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

end GoldbachRfc11PrimorialECPP
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


namespace GoldbachRfc11PrimorialECPP

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

end GoldbachRfc11PrimorialECPP
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


namespace GoldbachRfc11PrimorialECPP

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

end GoldbachRfc11PrimorialECPP


/- Lucas proof adapted from the project’s FiniteSharedLucasCertificates.lean. -/
private theorem sharedLucas :
    let checked := fun (nodes : List (ℕ × ℕ × List ℕ)) => ∀ entry ∈ nodes, let p := entry.1; let a := entry.2.1; let fs := entry.2.2; 2 < p ∧ fs.prod = p-1 ∧ Nat.powMod a (p-1) p = 1 % p ∧ (∀ r ∈ fs, 2 ≤ r ∧ r < p ∧ (r = 2 ∨ ∃ item ∈ nodes, item.1 = r) ∧ Nat.powMod a ((p-1)/r) p ≠ 1 % p); ∀ nodes : List (ℕ × ℕ × List ℕ), checked nodes → ∀ entry ∈ nodes, Nat.Prime entry.1 := by
  dsimp only
  intro nodes hchecked
  have sound : ∀ p : ℕ, ∀ entry ∈ nodes, entry.1 = p → p.Prime := by
    intro p
    induction p using Nat.strong_induction_on with
    | ind p ih =>
      intro entry hentry hvalue
      rcases entry with ⟨p', a, fs⟩
      dsimp only at hvalue
      subst p'
      obtain ⟨_, hprod, hpow, hfs⟩ := hchecked (p, a, fs) hentry
      have hfprime : ∀ r ∈ fs, Nat.Prime r := by
        intro r hr
        obtain ⟨_, hrlt, hsource, _⟩ := hfs r hr
        rcases hsource with rfl | ⟨item, hitem, hval⟩
        · exact Nat.prime_two
        · exact ih r hrlt item hitem hval
      refine lucas_primality p (a : ZMod p) ?_ ?_
      · have hmod : a ^ (p - 1) % p = 1 % p := by
          simpa only [Nat.powMod_def] using hpow
        have hc := (ZMod.natCast_eq_natCast_iff' (a ^ (p - 1)) 1 p).2 hmod
        simpa only [Nat.cast_pow, Nat.cast_one] using hc
      · intro q hq hqdiv
        have hqprod : q ∣ fs.prod := by rw [hprod]; exact hqdiv
        obtain ⟨r, hr, hrdiv⟩ := hq.prime.dvd_prod_iff.mp hqprod
        have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hq (hfprime r hr)).mp hrdiv
        subst r
        intro heq
        apply (hfs q hr).2.2.2
        rw [Nat.powMod_def]
        apply (ZMod.natCast_eq_natCast_iff' (a ^ ((p - 1) / q)) 1 p).1
        simpa only [Nat.cast_pow, Nat.cast_one] using heq
  intro entry hentry
  exact sound entry.1 entry hentry rfl
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000
set_option maxHeartbeats 50000000

def repair1Nodes : List (ℕ × ℕ × List ℕ) := [
  (3, 2, [2]),
  (5, 2, [2, 2]),
  (7, 3, [2, 3]),
  (11, 2, [2, 5]),
  (13, 2, [2, 2, 3]),
  (23, 5, [2, 11]),
  (47, 5, [2, 23]),
  (251, 6, [2, 5, 5, 5]),
  (42169, 11, [2, 2, 2, 3, 7, 251]),
  (309183109, 10, [2, 2, 3, 13, 47, 42169]),
  (22261183849, 13, [2, 2, 2, 3, 3, 309183109]),
  (12288173484649, 7, [2, 2, 2, 3, 23, 22261183849]),
  (147458081815789, 2, [2, 2, 3, 12288173484649])
]

private theorem repair1Base : Nat.Prime 147458081815789 := by
  apply sharedLucas repair1Nodes (by decide +kernel) (147458081815789, 2, [2, 2, 3, 12288173484649])
  decide

private theorem repair1Step0 : Nat.Prime 4068888119617109268913 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1597478300854824500754) (x := 3297421675813405104966) (y := 2367265082626951837446) (discrInv := 1584503781955009792084) (inverses := []) repair1Base (by decide +kernel)

private theorem repair1Step1 : Nat.Prime 727886520624378921284940935941 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 391515435415515955213579713375) (y := 168577020730141653546883149263) (discrInv := 700927760601253776052165345721) (inverses := []) repair1Step0 (by decide +kernel)

private theorem repair1Step2 : Nat.Prime 7220133498667649321394888991298148217 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 6974160016331034226978950939320150872) (x := 5312028798901568304215122498735763282) (y := 2150712532561334632206308424134164685) (discrInv := 3453076374363501969904147425367533878) (inverses := []) repair1Step1 (by decide +kernel)

private theorem repair1Step3 : Nat.Prime 12201180857128983238189192554814473348204001 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 5986102906477751078224871491937538629194307) (x := 1827031462692414522490428742824937846602182) (y := 9161793365095985719218867797936894472947032) (discrInv := 11393721984237654882977887138004872936106210) (inverses := []) repair1Step2 (by decide +kernel)

private theorem repair1Step4 : Nat.Prime 4754958795374307444704428826691173600731275520657 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 4562083915006060850818139921356560343959012849960) (x := 3982382468345064551686186272177983801153485645936) (y := 2982235087233862979746888892910295212278138802074) (discrInv := 4678873350304987312388604565973446911428587799060) (inverses := []) repair1Step3 (by decide +kernel)

private theorem repair1Step5 : Nat.Prime 534837993541724279347111500201137132745470949586528620733 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 320834060884239493478017714234038655743637423370719403374) (x := 69410184604146450487573510889483949380433088742635257808) (y := 176267500518306711807942043155886600170129412742349026828) (discrInv := 138661702029335924275177055607702219600677653596507420190) (inverses := []) repair1Step4 (by decide +kernel)

private theorem repair1Step6 : Nat.Prime 86596881003766983573517815374097591009391122309375802158218239103581 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 25462478001926701638824627565287741439342662466694943300444649816516) (x := 40852675294518635648382362514661562708116924207260727705899736412535) (y := 45891228677522158597661769145071547524196869274458375437360727867178) (discrInv := 85776138907473627933856485511619573392466505177354595990326522690817) (inverses := []) repair1Step5 (by decide +kernel)

private theorem repair1Step7 : Nat.Prime 162109361239051793249625350380310689575473171339507784100570119557621509 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 36177725824250495753458656824984573918048141996417333256444238566521897) (y := 52636233861017407495703962938477020126726574713801650321185608409201915) (discrInv := 120081008325223550555278037318748658944794941732968728963385273746386303) (inverses := []) repair1Step6 (by decide +kernel)

private theorem repair1Step8 : Nat.Prime 224845684038564837237230360977490926411487112639097262607069939488544862399 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 353465755684369009266210972860069871001362492509753380320440566014064446) (x := 11356407625310352914381775188072108714687368989524421878208086629116829355) (y := 44146251218076043494200358773352580308240009378196021845776315650341100774) (discrInv := 82222450102637928069871684725087859096903441482644263437723852218542986801) (inverses := []) repair1Step7 (by decide +kernel)

private theorem repair1Step9 : Nat.Prime 28186107012321888511458991814110032598284308951047638765731176314790757002488420395970728441483329 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1559918846658827307549420439998343076996850414575509632626949431935191587666225139916194843753777) (x := 26912182525729464795683969736334091221538454165517293996363190493368305674924949312441998521780087) (y := 9717304085192993682639389579633327910102154295177291672016022362936501558578708364797351007187198) (discrInv := 7219594807883108899377526105653874100516307831308591163986267575936087431507775449773635499163661) (inverses := []) repair1Step8 (by decide +kernel)

private theorem repair1Step10 : Nat.Prime 182335926262710296780628218045477800878301194604327769272706846160880649369394850457240436964826792437 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 3391094784) (b := 18052086324290228482542337762898155585803478560892925995919724585954381745091773868713514034491379285) (x := 79475811199592803008019344908217268354594499154231913671156387636501573239941126526219344851057992106) (y := 119079431189933821350518643354952950821091457720328039075508412713544636964097995525080395813664340798) (discrInv := 35815645575943248223796969889929705099023315056354035148509624770028595242507721027454368129591111397) (inverses := []) repair1Step9 (by decide +kernel)

private theorem repair1Step11 : Nat.Prime 2017874681756383524280966021581039590326581025543590745922348550180053647747852508836661453199594795100699531 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 474697279217238534763422850160776852427023845618062860925889662630597703803624526317868569819777434570930223) (x := 1683099973401461838254726072989070699253922713506516469406308901328078000900087583598921937088210636726582631) (y := 1455632616473901528997771125778076196516654531449849638932359537237103413783344097512957785486799137043011630) (discrInv := 1568905824727433177355941778499062112135419644612199799414000542020837911738381381635699716268282252221362954) (inverses := []) repair1Step10 (by decide +kernel)

private theorem repair1Step12 : Nat.Prime 964089392016639022899323809713399874295861128768121409355838289368215409542244296978360937002506806888745303039537133 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 419225615061926949467551187907802886683934903489699675198820005656012643318741454350582165834309818975509146345911632) (x := 939641610977964663067225113372402273839953029465275021835069353635946839864892353906066134254548490279007040090217436) (y := 897850931833666124812658813073009568406109658502467732430553937126407154623595444553896776544008374280290490997569679) (discrInv := 708039218124723388158826476025371093712783660048282453954235298598143923062437974449527609327624820601103950236077986) (inverses := []) repair1Step11 (by decide +kernel)

private theorem repair1Step13 : Nat.Prime 71313692327470788523862982204500188701664847694977940650051364917764957284129001802897763336967284713549845572263268338749 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 55757839787962309316003883298950517526894692105370607843559346312673638641198304313984025397929704201178103504797646155302) (b := 0) (x := 29802001395706842121533039629948232443625663045624470866782345488076794492992395636553186942315595036830244381541083083622) (y := 50800265221499969771786688106354591940410907382697324980551939104390746943862773550379931683569347183725803446768142900751) (discrInv := 49596306110725971590932461926987723732556096873831622285915519037050888302364076979944888017966068407069448662331045708200) (inverses := []) repair1Step12 (by decide +kernel)

private theorem repair1Step14 : Nat.Prime 1996783385169182078668163501726005283646615735459382338201438260862289012954330839994248084963201509785305591958131199409981 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2352859840512) (b := 954720214072476612071133173852174734615965084146647661942047924995468541530026724971048431971697420017324892242992642400270) (x := 1182314261760189331661847846160994367767985930825120462388557795744110069885118220012168621493591034815400727095452039852059) (y := 83050589081516146904488735066455325315065343144076002271867983845546165068003713769132871017344891637735123701823741551435) (discrInv := 387631113607370193593421886231163812890126168330664401648390566815582579319240780390154333570658259257037726358500912480072) (inverses := []) repair1Step13 (by decide +kernel)

private theorem repair1Step15 : Nat.Prime 18606743286950967594942073029090665566204931862562999188679347165322231631974091681097367712578647923771594125433593641495215290927826157737 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 18606743286950967594942073029090665566204931862562999188679347165322231631974091681097367712578647923771594125433593641495215290924435062953) (b := 18606743286950967594942073029090665566204931862562999188679347165322231631974091681097367712578647923771594125433593641495215212941689045161) (x := 17459031954731146535524392055253293671136923300058405428367102938851913320085482971729117865286582427023982380763457853377541660863117624148) (y := 18034274190949975355278412944407566788751217668733175521792263645243435192072836936628262070562297978411948972013866431991027332805703354757) (discrInv := 15539077986177704791160540051744506538204542348775988491760554916427702609480280134241069594773854630374597633442485472019273491452812465348) (inverses := []) repair1Step14 (by decide +kernel)

private theorem repair1Step16 : Nat.Prime 695332694161327572455253623152006135862488669358748900271003996013790223553485864815963634139189486771620597466839340528201236262113948166566202929 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 514393513807729732705109063801922479801445793042274993576531536991693582050689903146064477866393280003926045753293881414492304351083544452178334558) (b := 0) (x := 521002935577957445664594036752939954807102819057817393172268378097821815829926314183781407378451680781675953478565340735938307475853347455800983078) (y := 204839488802789728302115243820588488217223614252274001831581855962015044432207654266951408547478748541776787219056983170809508927881334116635818302) (discrInv := 379523392535863689617158140040125321559302010903206179117581801329984136251912444254143443880827624728943259028977105253356692576283792718055782329) (inverses := []) repair1Step15 (by decide +kernel)

private theorem repair1Step17 : Nat.Prime 92659339491244350977814642567613185658899377590077519701213721504801671400507495252141048682291992205125278227210551490382148559254907512080293770069827 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 50810826144200906450537400202343138950659684393538360808429512811565307335355401522584290916241119440056321956137740433302411790078871379183921970365186) (b := 45238085446539424821915082985115632929091562990845905794074140832969701237097347325195269019657157557388587040869560493507232302886699544661731404178617) (x := 86638538237591333815741546033462462017233653475912508340896057285541201307195466972831853017500168944399495013265795344481591107724661461666801777108016) (y := 86002055960936423552304412195842339633503740613317037001117270721240945728093052410605053741395467837192187909685999737315856162417696216107367750141924) (discrInv := 60217353281388877931718947279543091362868026455687780289496901155739331594619570123558649930724847210491281132078876996605962461838975086703024218185255) (inverses := []) repair1Step16 (by decide +kernel)

private theorem repair1Step18 : Nat.Prime 825780033545969655914284094562568710592111253082770855577216686050792495521322794041628360262542846948167712728866951252930271605489184840209970954628845389 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 825780033545969655914284094562568710592111253082770855577216686050792495521322794041628360262542846948167712728866951252930271605489184840209968601769004877) (b := 825780033545969655914284094562568710592111253082770855577216686050792495521322794041628360262542846948167712728866951252930271605489184838819487257522425677) (x := 405455565529405116664897897358408216139221752636256699152919442441188655583686844022701003071578475933329644735657292866850799023170618664884927764489694784) (y := 196003722764731278165700108818733968702166164157955236334399834259746981318155148967563687272408115145019747017751446473957239006914598962723559853195328393) (discrInv := 35749949104975388713491463947443407754412961984305683572773815473379126057952393585526208580125653581784304196354516699340095016845381915116401474959300809) (inverses := []) repair1Step17 (by decide +kernel)

private theorem repair1Step19 : Nat.Prime 2164262271766271798738365066801609234292464211183957231817580744486677505285958429284381153720922937434722277038873075911288916438364198154016586808449721863207756167 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1548814184807573953439301911257217277078456508779179505034099522256103660933599409690763933842666169616376762256575801405249432986780875061287174367880970196567405291) (b := 1480367817795208136161265096518272833814560813302118429031908841661910708241808913614833378928927422899020962484796563923365577884126691677458354441398598826569067674) (x := 77015927331200480462465410366020810613960560357129384723472408599602157688756918980674927785391953646306038277918229989147698461637453404482873440528052541991889329) (y := 1532689514030905977158169842987979279862461518933889590839093215887657131834552443501945350706025179415401306403162392921300569171671144616856745619896509875280984165) (discrInv := 685431748145869186860251767625930437621761335871723155367871220691047121083695017187423430383112373335766039267038352022946563754992625641091903304365627841701045648) (inverses := []) repair1Step18 (by decide +kernel)

private theorem repair1Step20 : Nat.Prime 3415205864847176898409140075412939371713508525248284511808142414799977103341242401414065211404106074423228094545208428678159252396087373148494194245043254304037350204049 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1016526941628131706075598494282779269463035574239518319245672478108113458466280558899768703988212990148177782564076758947150020447997616907288272833982319280414351056805) (b := 393299692748874232299874032349556912847218242380279546283094600391946987089605890171922335370604559921695517833787118671529178981740518350590925179157954006559262541135) (x := 2904844386263605156707016331251308100919816859871399134610496623103358247531933685873078563701597202691592259677432180921011714317150132482936800783732970509657246589634) (y := 297610187051369399499692135965135207783925546843348594839915943850748731168592198619992917437992624259499106285621619064376742444131296080178846731005321621500062855737) (discrInv := 2964736668317657435154019510794528278712306229738028383400407736865385950028145724822450833212552926612969977680171830004669870053877001759772949160972766635009432870681) (inverses := []) repair1Step19 (by decide +kernel)

private theorem repair1Step21 : Nat.Prime 328303739787759115244070635449445861802819574532117590120116730334721798944193632047933738783321023161394806192983239416391472951288261147785086086162803483961687954651513489 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 260872650859921395984191772770400758985130502969173423044953680670855519905765833140687987983377790078882318588283622421843966176803799936482946628007586641134634364343986534) (b := 0) (x := 94906086307483290213034365021348364833050000374913462854247006472533829898999159701844880450057634654931914133594761926610837587415081831316500470083329581798474629944607724) (y := 225872697110010181396977972940340050081348144943528161902668612123770551180792297639455639622979344771372006913407064554363792584235837038375947669020867357689723092904606617) (discrInv := 92788570473650426754964510365015141229106387565057627401679497762824494499368017260785610157379902579713856993491089355610543346150688010586933441243698704968744480246026731) (inverses := []) repair1Step20 (by decide +kernel)

private theorem repair1Step22 : Nat.Prime 18442790886317156057950912017008070732635192418916237742587677443283331777489021473924725582388624260479247309932413926787278756464883850025421874220520714459383651725678434051903 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 18442790886317156057950912017008070732635192418916237742587677443283331777489021473924725582388624260479247309932413926787278756464883850025421874220520714459383651725678382384028) (b := 175774110750) (x := 10462387092531344942282780995308896109201951371637214653574253226738075884907498540681019352059954579173902879229977920170044021892315291255487594826339647144063695542812344070893) (y := 1921069371068804908770147498530101415028570368875387832840307718243810933636920763822206762745962924141180501259542865314225804075291238313162167036597186487650934841778364356077) (discrInv := 3264858262509716943839499284412133238586773649213940720894758067772173655954884793511938793730498280614195774095122498290941361816309918327593235527312855194613749412466882725808) (inverses := []) repair1Step21 (by decide +kernel)

private theorem repair1Step23 : Nat.Prime 99763868599062386582369971251070659255675455907029724034551323563319703452386659735975186646017616909949398095846966257271600141705073790694278549835338374475803001723286057148770038985438084661 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 99763868599062386582369971251070659255675455907029724034551323563319703452386659735975186646017616909949398095846966257271600141705073790694278549835338374475596224044177729120069844966224772661) (b := 99763868599062386582369971251070659255675455907029724034551323563319703452386659735975186646017616909949398095846966257271600141705073790694242358584095065285469184859827963332991982515958660661) (x := 38622243688208504013462376268207267671726312274314517110093783263192650045529440657723258092167569622440124094351651418712312268789503134649830635251534302544644691080160379797216617395680036857) (y := 89928590575256741074648745549635610602664701520704878513198144931246300849161289256025054136243760811177356764176464064209739919663252975250801515858478939352103392882484578493448051636525870548) (discrInv := 66035681270220746116453484575356392459274395635084395827458774040029432759414736527122679625609883804127339027384899966087031238842592438095777295992126947779261010002034743689959076661058941643) (inverses := []) repair1Step22 (by decide +kernel)

private theorem repair1Step24 : Nat.Prime 1097402554589686252406069683761777251812430014977326964380064559196516737976253257095727053106193720974475462551802041936817711167405731005075742559426762065073236424224443868986786921021183100481 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 741637340886436745516479295079062376401095674643916174352545622438483125039604743567240787984366612589358441003207709666538017710675218213975244261352660585378817779976295584494031835757288425358) (b := 412578064073877616509301902812713153383210663915207551764697100345223470633556699951122511263591634635715972075954261656378404075399618751889810672356953391898451692139273748374833344180291426438) (x := 777959031691275590413311792570377393890197101754321796506637907982574524522626336289231542056529614429488884704098817443045695785584283887955523532880063341026581763501266771390964199738235873514) (y := 712562630772986351331867442963826492145258642716038094242507178650200342539568475548414023458750087914851251547439507538895960105836590006821831174740541646602480889484144048349082115872886029457) (discrInv := 761160625713871354799098033783762443675761399332889253350249510992179653398950217108597213973391848380029176645432421222287520509890958424811190502608501302514359335988834865281716570628470529480) (inverses := []) repair1Step23 (by decide +kernel)

private theorem repair1Step25 : Nat.Prime 32399713021705896916036801343382711582510183762190601296357026045717960172010901162494245515907263428511465587855357934895257428811920494485786997590123595919267754316327437641941836294630757102857893 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 17228078033500774912583212381463969739800689547456571871366965931967306395544308560833319076591866966700384449623675661164514270678373502036305515853529170836542933073310489585526105772998040243991143) (b := 28079469298308612556993735389624092176958693686010410058964248898238451672740533673688354042885552883721437292983159016762130701673386828799348371576915891927483925150940812726912329983762295480136475) (x := 12534167284200443219831056749218218017591828288724053065591631351834703894311774310455123280504982017561514024785102233161944317284170365755283361317075547340092039765364581985266807541064634687479094) (y := 20001134089699409007091079571134484370179028512962807393026984436270939808843232959590089160934563720574953873670561905057618365859471679496754341124534365289430068163600736475262217016733221828337149) (discrInv := 10252055704013757572134192218669836325076740176171733104176319211651811314255709703858332055971320735375197839257592561630536206620761557351750071701714210209628593291511239201630823233487128425845683) (inverses := []) repair1Step24 (by decide +kernel)

private theorem repair1Step26 : Nat.Prime 11918688031016818063120961889382137813588526239494483355283081029281991700716618145239783132463709553859132875924163566703424887679259458398044833687825500475504365993504155085816918497523300188710740983893 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 3371753180977870743573182656281204349347627114838955741930262931646198104979939135306554003351684252702734717776180382194558608171109648358994432093434036061768615844690937203628043208809712539570324772670) (b := 4282438127825019796897906737278079313355770497377168431410697741613964198973224891665355028083105533410797503609075188924415226891295535937539193355937323176227681238207829410837675954063811419360618726137) (x := 1067225019530204211189867446759278623261375270099819860315744908323710671332327489204060957999803331340996276182062626482152595803720787438605795882427332512239519303954620242102193043148130112873814217457) (y := 9755675872518017864785951467966846250707407166502462937584273943801658498750957931789112857514118950040217239713392398968572171042416403854658249108779445303621846692018656008914367962835317832103391473611) (discrInv := 5232992011292880864938675675217102567691179381932313321710753322192556294546778476355530333272291848313873714555145768143021661981972853752744334270509996169773417313521177364589613215403605521177806217464) (inverses := []) repair1Step25 (by decide +kernel)

private theorem repair1Step27 : Nat.Prime 655527841705924993471652903916017579747368943172196584540569456610509543539413997988188072285504025462254302857478810809896618737542966088740998184758087328503986868174613471315237158838824319298783247756039 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 655527841705924993471652903916017579747368943172196584540569456610509543539413997988188072285504025462254302857478810809896618737542966088740998184758087328503986868174613471315237158838824319296430387915527) (b := 1390483697106419712) (x := 10162048100744368197012585490757273125726399647607690546175865970610649028251171178333703654821225982337161419695121703807758813562615620463940156337437930981439092334729029291990214652714961996705804799382) (y := 217414900895914768006408435817151356949788774396340322444366305830738294189133563658714768568007157031140568016088807339971945777594564147828753385335918691652771208801037188123757364034609901567882583650809) (discrInv := 262662059354573143483050468177040179068271146338486988617583927805967486373298069944152468224164924793394226228662974618540545137272056929608159025429781062078878898915592251100419865405710006377051630078610) (inverses := []) repair1Step26 (by decide +kernel)

private theorem repair1Step28 : Nat.Prime 881853417749787538942695370563350061278206302384999660729292845491484237013201456691595921558580288781275895605108195259323940670967531370732777348791115426695710890601275509881860075748646203087194126324648526961 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 91779941369611344028965138297021406086198802185083727320757127133570175437108151624181461762636869479835977085651734455393054599986358204434884508145051652134260310125194059605268197421715095556341310990812084868) (x := 594060659893348992037830140710094380656208537421288978836112264346734941289643437000616849882319025786881572797444543087760614885094798729026982977230179500825120098976393449170398263552340763450045252495968502203) (y := 331100547636841893436468764989012012006665300468433171371252217761587631355135129879658855099404520399578544446834552011440697877527691016256852535472860886345284092646829395059564523935447576478906124460405024469) (discrInv := 253374750526217095066016883186664158336801106661255215032500101599039961582115708998873016116473357299458958531202075479662540111980368956791028130990567133185040793768220044950326655209599454698768209136901317518) (inverses := []) repair1Step27 (by decide +kernel)

private theorem repair1Step29 : Nat.Prime 69666420002233215576472934274504654840978297888414973197614134793827254724042915078636077803127842813720796233803192346382868979271886737524201331708001674533338435866811723629585446471191221475246831087314100834207 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 58871675346875196891794808993223589629669002567391748003149972604661819387322177015450268422253232795318806466280235436030604015935636626739019900752928031026012803615931182835510422569725414502130585841949929039366) (x := 60923654188034342068130559822602715700221270791083102206186846229042387887407471235435551318700708726937379032065982425042919350323008471810995477718221511737762779306981684498388156890228610144762901731638420960469) (y := 60190841741674221327898070499902067460704499300763226754094924787878227049800536927756102954337706138799181809273923675678177303129517730968122565907574359459748048729119381043463988035840884922749487468371445171045) (discrInv := 16143214417879508183147559714878371792918536317010944795560483520631122545906589818773064236904191309122434867370257180679333940222442514446310555936576151774615535176685165176476526066451996922415286452561384827920) (inverses := []) repair1Step28 (by decide +kernel)

private theorem repair1Step30 : Nat.Prime 456812899234587760968520274239675794686702114734095924650218123496436392543026916971599636547873904132607028101246906950632778671763070220597025634287852987155589166160097298863176783250252984844725853609734910444822012660571 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 442787891114847734640217427914329821477462682812513909611943291231690824639821814988973040049715384076574632990194911539786311707599603243757953104595058210453721793559569321518888088906643882331984269054520289614107865905229) (b := 243989287275942068647918083709321152839483601713321108113422185399239333355719908212917224111835036574192292762147195891398224063632009307854062002196541059025006707514945413251084772522778537695662366845363705757168308039689) (x := 141230119855017207675774024488003421267949308561967810784963375323717878174264327875499357717358187541529060090513563414434038547151611638481458724456627985193122677380989793200712614765431386775339904802815393880457136161431) (y := 228849666113737234899063046593834581623273364719233334309145540326953023558812391804489095043607392350481766601365012792367190121123113115725772259179514551317431542120125081672644097599845877773600347301036003061346089277643) (discrInv := 443408737282910270651775592588436434633119756640649257642283689215882652433021736322736926414254028866804309562976394793660276767175764834581646786144624817443845942073291107058551861125603038202602157252408987458075047391013) (inverses := []) repair1Step29 (by decide +kernel)

private theorem repair1Step31 : Nat.Prime 28700476402850787457031043410089117983034147191400878101361730492370335004917362884409871120769046605083767925512768601636284048397443172783599679809428223611439965086692817983774011540936173821005572633677509858873866333243166272566659 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 14286865023958990109548191015821876127363964349292092321032854021442680395624589053256935187686835553220458235544796336141004571665674549043123067627760394477020757189649116599376614814591578743568323066813773702389274296072765157271568) (b := 7589426196327822442347179643652982833326957574150542971726573528253443254032641744271569807406491290589114746869901198900065206389466918046281576052375089412508272079752306289091573909431098278048233220705853223911459132294348402365293) (x := 13803973341889411802245128643813397173316586049101998065088872903104715758319770471162773381781123899741431801738521132957757545586058367171687437827058089409971903761284595322886926274842353522732648002864109039692249745161136745373228) (y := 11006724522493865940394598754920229926285236833165888988770207618155713535078322999270558361396907555050539945235092252628204786377653444846725843049394793276063593621394157947678106039903738479690964010868853728013552798447873884707778) (discrInv := 17414572588390998273312822260626457444250272571225741673605067872954485146231725881186380674137202417149444413986031988579414495772531381422174747547294302785058987827762828799372176477137803258562416278775044261118557791572451436594005) (inverses := []) repair1Step30 (by decide +kernel)

private theorem repair1Step32 : Nat.Prime 189766804430032400336444870422125786289944611323564937133998326661395576222551098374523247724485922035308632074830459107548094946196808508241120253303844410181096524636769266678042549288474777526871284142952016865908031550264571519683936143185438729 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 189766804430032400336444870422125786289944611323564937133998326661395576222551098374523247724485922035308632074830459107548094946196808508241120253303844410181096524636769266678042549288474777526871284142952016865701253871156243490983742123972126729) (b := 189766804430032400336444870422125786289944611323564937133998326661395576222551098374523247724485922035308632074830459107548094946196808508241120253303844410181096524636769266678042549288474777526835092891708707675574214686806477703905879673706014729) (x := 52956949457463214838507528093141567721281256415066977856153312238529153991769098927136455064358887693995040670585500417195379741518409499442941476466795309843768102445506240021456788773664647821144383307021414780078082645429461210879518622647968209) (y := 16331206935354251203513373753880948013282787803515296898102733717824381145147279410320847898823668547176750505008521441683023067144102976166486840021143766405566209466686022959868280268288534098171717354542795977604307219272700874434083240590636664) (discrInv := 52624428797777908087038034388291622846187923015761497580800673763763987185199159184367451592345217924572094709487722952120922231131198503050759666315676755521172897957021330775183656272354516286915512058035595759587040364737696583313115982858161395) (inverses := []) repair1Step31 (by decide +kernel)

private theorem repair1Step33 : Nat.Prime 25602224431555172252312514552147655954776900063343220566851570274064209761109915262331837032237357570537221752209492133304630687338286708994365586605461160782287890350047167749122612067644949875457916068813780925509297077944155841156268892288912769388668047431 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 25602224431555172252312514552147655954776900063343220566851570274064209761109915262331837032237357570537221752209492133304630687338286708994365586605461160782287890350047167749122612067644949875457916068813780925509297077943949063477160564260212575369454735431) (b := 36191251243309190333816863458093815778056469479424000) (x := 20159176528770347677103446581454784651696463608556838514638881380369480315272932023819036838000996595209604526938025776407768974416202238205225967921067715321007884694446490088469194934727185660240067189023974506899511663501853816759034981737621190435469367903) (y := 9404106468970868734935687495130002915928944670522156023528677252151671575466579274606620443763666425198559231930170876568276248112358046478086033357920235839273074298382151575829533605895219834537869249323340726766418228772645084670802664355389381115996032735) (discrInv := 8639084519533974295493199520235328723964708556957359246124957617780641902410397467419854308588712621838042404785489319100517427960308314530258710943112378081436478933708878741828784502552827084042497924943257723795331599117765207190562324625198997563785459167) (inverses := []) repair1Step32 (by decide +kernel)

private theorem repair1Step34 : Nat.Prime 716862284083544823064750407460134366733753201773610175871843967673797873311077627345291436902646011975042209061865779732529659245418798331866919574039935616927666033318501080450059286705091500645947563533127798886778700089309148695246023116510745730909012865121 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 215126183294928110246220200510339928227598828285751043740853337345422467052072210202390959613699396973468002136591233141917518069919349507651419972604703506605305886362283390227144378776656166026196175984677691300848670484335531146615841512354259651541017842404) (b := 376009305367331751093598228354864407556816601729887539581804266192533344220834734357972062432226415132205784856239389674138662445277364380621951981680595016158927033106027085060395212259335882549827524150909907161916102638873533224135993337677552347569061984826) (x := 74276225786364636947951550144200408411205628675853800927271512298385401403986530565601435817492849143788496029064285860002534335881722962953572573996866958564242682801110518292708556826626839999925384438695214047430558595988100393924971092464733085837762417390) (y := 600018236630702783315790079856526319010438069971486617293018374251725225974610936549807393792461004548913352781911055291341120664754201991133274855001031372922459941209539001429438458183698529066689916035326513244461162829760731652539457142448829984577895678293) (discrInv := 440688109243093157298774704265854419516689637707730349877235620116091231279765947550338506746578716386042416288683756324349592755715774011360445122517305233548516599621972603227513302326468744817618143073136744126294592998074234930223447006478521200907923126503) (inverses := []) repair1Step33 (by decide +kernel)

private theorem repair1Step35 : Nat.Prime 59499569578934220314374283819191152438901515747209644597363049316925223484819443069659189262919618993928503352134859717799961717369374557103454546739417432092427321393454420625320686102048097084709072965856967477733115129382678969559743464438061645366024843028669 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 59499569578934220314374283819191152438901515747209644597363049316925223484819443069659189262919618993928503352134859717799961717369374557103454546739417432092427321393454420625320686102048097084709072965856967477733115129382678969559743464373059933383967747860669) (b := 59499569578934220314374283819191152438901515747209644597363049316925223484819443069659189262919618993928503352134859717799961717369374557103454546739417432092427321393454420625320686102048097084709072965856967477733115129382678963180997469387646004837120585492669) (x := 19439819653791633198171793662434853599337040214307389157225955691521512332885520677773562940598107004826051839608620948491810427103603662273500771511155486165082659676572664944861672760535245980839479105549871879926492835951451558191775253644002455437136204840464) (y := 33124283746453544322312912462135991960235235272171942614166266924121055010603235562403521482380178958726880233788186215102910238562615291674054468599974137756471513952695911322092391141855777008071664084195627990834462135276879846766325200068171966475781704069461) (discrInv := 11522831382293098177913586872280130128138969572675019639145050967301862281730390751027805532388424276746343931689666558819628323669724050496896041212921863544052289529605236322574909784623188977325165411533993701660772108115586368579450859397397490671425166678179) (inverses := []) repair1Step34 (by decide +kernel)

private theorem repair1Step36 : Nat.Prime 1546988809052289728173731379298969963411439409427450759531439282240055810605305519811138920835910093842141087155506352662799004651604818353722775110704550825246273418844749586120969437051607915140875486892691459524023899270629183511140177002731769753871148643684123 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 310941229128833676311557566786949036418585334459955818108189552621214674212129136418249125756855594370600849208134585255840135741334778979976857541240290748751769097812730133538612221961294673533247882475967270013886337763704698160795315071131694575289814703416632) (b := 1369093034395407557594484904077427712865557745251502384386256949483224259517159176813094083799416883802727446601989852447905645619268541587828852518269753582237369402393912402422996035869677116391489712981107954513575746897699629185816855960031228202443268260787015) (x := 629669008845172861924712241638846747625921602427139910902448534824888036847951172981472266430080855627066244571401358705677598729333507917623185316256193195954291901540290062790808453956931334887668456572854138277187797354874678657527470017533646516149033997944289) (y := 1051845983221169677528336286349376977039677788402123968178567597038764418680222147900862314524526005104114424602212286180179850675202923525084727279305830404467416299802181314346832613410229711170935447292166906671871456711803806976647206727022253713130452622293548) (discrInv := 947334615684150029638672382029328265211393441202654787910832407354228214740455786958039162279890006426310966464286295375778166605590800169845624418560060404947498160447383407062185866384878092691665150418102977248774448670989085733018075624020022754183398657681059) (inverses := []) repair1Step35 (by decide +kernel)

private theorem repair1Step37 : Nat.Prime 522667186015215659850505057541329290808152330308567941066051607336907496226919128228911206932541420215599629847446531817005934510595854425168683243353626179104712267458733321310817797776599192173422001327250033797795953948579836179398342085369491491385599798040646814861 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 30128782413400823103465121964758271132936560467551906777363258361730709951016580166431513972644401361878023485748762545556127746860641506500797625537484059983540570783040532663932305206330093560948113581821920664762240096338935341766676912778718155575071832724473532095) (x := 126329489446737079672301990911159392847288036719521477814454401506221426849391980876817006014699540735229445992703639167764735883062718933007469785300687107260075948413536961236475171967909202397971834796260364383866101919528046338299704611936704550682078924265967940910) (y := 463353533637259900977368538544205767852605268666148598453781807139695761706464839355044309048994790103375091182714981376475422466441004699674993389694517271736956261256076525344851202115323209473903240392208833468847578535447995744401133526979567606176822075874394765529) (discrInv := 365778948545754020270676461145386880154841822902438747082231181887385682761918859469581644101521341722319264752588253485653360962618201200171702677119746490699891473176081663526505836385685237014842638866115698368079899339704747691242132354229104616957881526220815650309) (inverses := []) repair1Step36 (by decide +kernel)

private theorem repair1Step38 : Nat.Prime 76411738507901103305706249832714690530532532712735721752849269453027736209463987629103077134977921108351616700057616269621595311423282734258977038211121355815198442241050442634001585009280270880273155789709154574660071236200457814411378318303300838882921000636305122536467705209 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 48187653386074607155269247512211413083616653870843161230139585065471347446396580855709896687333892252273119392744554516219264150532966928995664453962013674641362874464433874615768102885230478589069099191802666884978156057495491302468618433436991653653254549268247115429108269923) (b := 53061270303328096255706703477568247926665970997553450330174030164087496445111867680542475707144089359291571617193344591167176529048221851112514606776068374247513926416095914761389961914944060720425257746380493032200570282480746719438123443382361993739573917926566203986371972409) (x := 25981243083567438636195446774374830235108258476729407912849424747264059973278116764595273756129053511723074361549977222338999563930688686423126164358416695912000261687073153134769897296726523790871837408798561378950785642087504781256083059194696413148516425242709890670432892935) (y := 54106103424076523483334605216919290404266893715708228290078094562368373903248013590478814028651251511413053897766771449011138318554937889028560932053694731295202450204785485259760829248052399267583912481536493577363298747435748534580064785147701529378040765157437577391569792059) (discrInv := 49073819019309480739552437185087925484187256535499457267519560017255753821095274400297057738003139477033410948792763833211097091832983663220509531198670790903978098031934749401109971700839133817171001431510698853930935793134670720795684574900168099319393672669251440623626827863) (inverses := []) repair1Step37 (by decide +kernel)

private theorem repair1Step39 : Nat.Prime 1040716416716836841858223266784099177822273515667553619915544122559819813012468091910239545116829038807582766712279724949805684902288397348197126978236747621185791601518954880206530909497718948532085414192487614298731619436488759772599055932949451196513661748145981813122747710604528807 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 793749215520544417559741361820097570801815682197527529261721443534024531907536804888438559060109006905983208502520753546291141633117959506750200044541046056487689993025837680813935415795202410978724970058569077028820853883612209135879602927795180131616170144560327051778013535815455885) (b := 439327062318582374666661586547719181480420529609740667655103724066887961432502255724686699009737555755147226597667832029529589920440651458585180839314697465089350161787633255210738896686980570404841888731457885663098598645472625465036006154310539612456204347195411901929177831755111013) (x := 970118871962188215023655291362169260878890517964816894772032819954674525316328996690159874644486565689307994823356514723323152312732574944138999971440687316158537873851439190387559885365436310016549318558557601389034982959125984893492345533741161941669137268025376591126157058865496296) (y := 1037615408627501082999781091055603446802225300076744038684523209888306525952924250300832909189493930538604620334996601885558210380806779070825539579514366877922869144612599722647439010086011076077964107024711899446254084847702734367845509660898616416104151464238411752139924680214803850) (discrInv := 1018870585028521238637728352145050912501606984612755828676529007275660870054476382950056839159194775476629146132793717244608536838804021491634746182874770468808992034306199666558932676873780856016689893471934037443428642902419703816600628991864747969249662759353000761253418623601434471) (inverses := []) repair1Step38 (by decide +kernel)

private theorem repair1Step40 : Nat.Prime 37487646046557179880575060292830036484336114307860948942977814838727269484522113138698738654653298806887938839743027972416950575865330360879408723087082416804849224817202118736970903842785556632259845353776872809082784263743775273143381508248848897689672125800384932859063529021433637552221 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 27169979049717292628440184794250195828697315318124262812184145462568506182092720671872161693010827417538187503796524319225338133047041153692189438481032627084362922098408789555679110397367747378192251124080940662104831663193840873794329975101620674156388368250406179366104498445872820419214) (b := 18209058926595871578734856178531161694888545553553716580372284400658662817177545391464736929837320113207525330423856998452879973320460804586551400652408435268004470858603507081486737288605877788586776693000677416608603217762513213353035593093500288381211714235723069456531902040703839649839) (x := 12920869611420897182541245878871374794591668803405377192149697385140329577053409532490334190716919359727190059546795768705527049818643160784908233089854004207242298692843064155207793714544462486478824352674538078308332777015671254903449645229945545396386992543774366529714299571638157739350) (y := 4490539699156778749533145368802195675575578047294581766223826467528320844268101879099176201620330479244899152715337532583282316685763544242528242848099909176437081238059041427623373166100573321780332296584092992696243050517719415281024465420879454566380618977555535855970320337440675621737) (discrInv := 3878117315587445146548360000077783149313594341388689039248999008621717470646431675202726652876872417203092596595051213281476663379253217201672044875405541980791787853810576538531062032376297289958714597917747005796498174771544192078408048356047627386612589577889159253467048711119441028212) (inverses := []) repair1Step39 (by decide +kernel)

private theorem repair1Step41 : Nat.Prime 31656217778138931207072326213918567328978725710587331169203957873674210352587791307295317664490050257683678625587961513139659412086023031262451419769245754257476616757626953676303067436384031004412289314478412709234437628725965871898451176056449501362030594741904142250938529771976490840418073111 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 17753359098841574499004687495739203687785059153431254436221639589313394522198854216684514810992237437994561344556603588288683788875417685712506532607410059353769108118807187695168431578899662780706112693453997973893461952234327508026616649138582097608470219810116876457232128892297964528764074864) (b := 6367553046288584415237052941001551882961898426361869842938764004218059054040518303411822372303511674491157324768417279677615335178088387939748731112452386870200048632370449090304542555411030400147598847998240008871293683633215089911564655540135875135016973838520106577441526143675775357314991664) (x := 84978452093681263440202200932972664135974419520232755285300503040385444812335869859572362181277126982243813833875207601287643838211855202292791103039462593128733968833524568695462845317994441153580150116029266243135874733700948781749601607855416706385245074232851230573196601276897955884119570) (y := 8438817639402047334085480461906152464414328386700009408458657961900500710408491763647733485447451062621308614820542710930732537216280111448560397180778755731419938435936031884669040167120888174913299805885831955813047265872360903582910729128517248053524196179766001538701297410050378225878849954) (discrInv := 18879376299905432360352487971894301803972413168233558921531944981766449001137694185007248114702249421484874714180007485505775516013818308656212764367995677723540398947922122105923092657541381346301211936658351116856585434206507919476986153264114492339770417114336768223474996283257005107432406352) (inverses := []) repair1Step40 (by decide +kernel)

private theorem repair1Step42 : Nat.Prime 458413689645229862809614355903754773490940927015015142661242513968676240115823805920943495099480417781517350177139270671775407946417699515711559009678101565474617953035426465399658603970590958789588836314241565764441269215329599213700630743705397516102691052196774375294512754489135550978689633501921 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 331373979687370091200541716074489641057901613851937977268704144542646200513977260272764906799749768991590582902810737546148342523186585562797194477632756697237436986884998917028120921142993774258415548403649991815758995590279883084186313894784643613935361409778438070073049606963961588452063469724704) (x := 303353830792616960214540593050554043133169029338472965574666589553433754245071902846797166152713313721391910396343802606744425368553380758773164913439581430258736307871908618684626961799787393752239435380609170036550092349819469145418930792035250843549130913287625959419809616332463129899641280595503) (y := 317843560162525286648308244839398439575989621545872834241290271904992687303916825743249693889119847425071936808136397528539737315833198735144028675728239153166141387348446342048746299128679041981723755685489961659716816637719538168892131382207193904287176648937594872434323595890319695521267571503046) (discrInv := 44022077569272995757316518632394532913751178054925946843181852287330956832891405126364629847670088046179628674587750895007764674043740980412489215234540860482538360789150478563227042914198168584620655888904443481017436295386182436198329799448296830266276613154463768538503285704707059540284556720335) (inverses := []) repair1Step41 (by decide +kernel)

private theorem repair1Step43 : Nat.Prime 51603399836518703041546883236907722974488474683616747101804739176196900011718227920617648771600960889456517350765479129886421784824267225633892341939959045360713916230265374907936515751774496707049924495055880990471750000344309057310268718839580582393633597090797033048707119244990993184903697769350079349703 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 31426414618855942867145714774582322451582302347602028499879463445595580055055959682557983721967547445871666213059096287899389449360908345661207867194876585829287156543257551480384680260802340939979951961449642154534670943643493753499482125449684731326990303862416245310934365054371627997144979753820216504653) (b := 48942545844503353365893510435575102413806123495807109441616563935084799606077258443480708843330152946693361691709692235712762760779046911692347740223114611989788642546794727880435443743286450632577818078682729358012219583040478576114944673143081576746031390737904626068677205547953039481997163484813079487501) (x := 43525116929624311010918290690060276253107161730068877840697212953859367463770256834585488962801598082655213927819191812408697243575178345035186632149508915021427693542815185510840033494780986867087039126227294374998386550713195394699393738898913071329122551704549336033708615428217328551084571858592848306235) (y := 50265535210186984376125830881027664920803665985604222245644655634759197123344900910969870031050508924741216007442855222202988119073083223486448867657256176207688139334767432998446083882353166756983328192630944438037033864792118535947625000925931793437865044425847488047838909744672933737143555684958866487871) (discrInv := 8538704560133153492468384826573530811672103076186899482189451444413604896715408934969937387422119749146187071525949382545656085439953203062478427006909471134963106334571860576050829452910652960962935731725266361917717024840660190082117360566357757721487716090064369553276806202700350494599729803817732400573) (inverses := []) repair1Step42 (by decide +kernel)

private theorem repair1Step44 : Nat.Prime 103206799673037406083093766473815445948976949367233494203609478352393800023436455841235297543201921778913034701530958259772843569648534451267784683879918085162837330644233141539247380969377750009033955052561895098864779318321693945319791581816267002812340086044584625023317355078066570444696295062716311400139 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 82995644128275164478675624129784266475625661044879885175113887947631995899690986586957001812261188374359409983089590400833324895744839627914099838861242671246729394301822947879988639165691836054732987607202177109084188609082250004641880275830236719363821126742478557397728578825074892351035321030905344483906) (b := 70957990691357271467226377295428984834217482398317315178697228713240807504261899541350344612866016228526721708112095153686066645991238443641073694709353256492280964224172865901762712624350325363492789802958415613788215898903018432196455042660160114619889116710306735243178364034897777200458108844304408775466) (x := 70993116417638764287935416570958789525202859339879100143159851311695895177163214301816006422263862444093226709127680417274216560884433822506726446764460781693539311426930704319753054946135264744221181721220244369794786974178882235979628826439708819934179984792970913107757426954514692386004148735025901713914) (y := 19931401345735616533456267048805664790602228789420747865695431707961598050142402273112757861682027495390185826449871119318505965135591733470669508470791697701632940105141867405081597627857387844370136914339523917321335781598782571386911903394110967967918592997294689041959666254342880065603498203305305309758) (discrInv := 62312112977942405709808853863482336250320078229134775965262433831936724991597726479363250951629050504152251712942714461902049133646986633611309732257127427327923060323499710546751684574309023580383699273209400628719087860343515212155917194157812622182167091685052698582461493423967313742156962744828604900378) (inverses := []) repair1Step43 (by decide +kernel)

private theorem repair1Step45 : Nat.Prime 94743842099848338784280077622962579381160839519120347678913501127497508421514666462254003144659364193042165856005419682471470396937354626263826339801764802498940330208624781106921296354987572407214406720851803425193356217233738639201060507840536329584825933598996052574744517563562715397354778218200136726782779 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 94743842099848338784280077622962579381160839519120347678913501127497508421514666462254003144659364193042165856005419682471470396937354626263826339801764802498940330208624781106921296354987572407214406720851803425193356217233738639201060507840536329584825933598996052574744517563562715397354778218200136576254779) (b := 94743842099848338784280077622962579381160839519120347678913501127497508421514666462254003144659364193042165856005419682471470396937354626263826339801764802498940330208624781106921296354987572407214406720851803425193356217233738639201060507840536329584825933598996052574744517563562715397354778218199507319038779) (x := 56392427508284462228754251743171017146491327489696028899341097781822973397173838723681032293948115838447895195635868825727627939589798359889888508429329268393047475495978494688754537207094740189175988761847965904916669870186750671423418260878945546386214457076466689070811143818888844311477726464068952463607751) (y := 44414289398638425324351297302824616699778467870900512896293700719201669315958776564673447351282515125211308705549184404772065200359368873478766190859639818391388412407462560076341300275081874637776215779436772129146657920576687785069896709826968585149091933503068281770713978168118730391615501817205808443577478) (discrInv := 52063364665173223944198637329549552753215277337263265654560296668246725817915162407246437772281262040109034068480771713007625532731303531412442504852542297273693787643761699314116880759755741242382875907456697366057713047732640969694964647568324100554400406701472879576656008206312532542746011589496769976490503) (inverses := []) repair1Step44 (by decide +kernel)

private theorem repair1Step46 : Nat.Prime 45856019576326595971591557569513888420481846327254248276594134545708794076013098567730937522015132269432408274306623126316191672117679639111691948464054164416515144355873206713575535849566158598868040044509472499731165162807446820516058106180950054381123902023335571515849808584006101534360431403322650558714878953 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 13923289887777772115034628204135710674131286411448126881341524248577685414580373898125015420087037008099405526749145227880908557996447576992837477180193464372106824632623333125625061813682593005273834831324683879265014722135284465826805194125900646613240456650928971109785364766839001439560816196201712898721383104) (b := 15954398534236049273658423573162986742850288929322145386212627054491097396812190974364087154972910617297191760858210435229616443349510707719794011772951827402550003636794067962518074587359962760680567681891690890836981656578612770638446939220864430413581083423467802448180260944153807556147840598687065235379819583) (x := 40568637975521153917433069780389733013406880979551091928064628009208223156297441174428893214951470490894609481554912259353378805233488660498635394939182260678340385182342557768234438906250238004101768768801533259521101909246816047068503556053291824261620802250239756920733167567890908883378967532426285861163040245) (y := 23156712556026329166755398826024275351246046935945254442214054534683250189441501691969821026772588553198726108429531639676153327493607751887328109307240441809998890525815767568985987289395275737265084553906761731255932961596705342295285731071027758168575027746193155222009440380878097235344406884898677750179796989) (discrInv := 27687614990614817572553118211500989895153427492681383162328503352436141782218211798519951474800605729481605456440688400583042594727806856867178102818843134135338906677308384753434625053577245910776654538844925158863071450757803593791749499872042873176222408564468396401207127101897743149812021986673294954126599204) (inverses := []) repair1Step45 (by decide +kernel)

private theorem repair1Step47 : Nat.Prime 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507211873 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 175548816910761473262754046571695545634001119691039890814170546254624348151020270896037653661838110217023432442966862968034438439225882421711641267245196995098690786866736653107716142309327279190195766810838703459916776373406045164616032933369789484032811486100064122540976156885678462784384558680602955663494086754) (b := 265445279205659989285503333500022813547515363299232456227818158756116103015669828822141163249183630656153973592484746832228859005603701192350979907439670761548034560994428496905593846638204997893932088833462659796126912966257162279867750088270809655819935735468287880745366461985964770752755593724588402830581519495) (x := 548571004392727968681302678776629661416418305171021560544334131146447904154638065344116029165266216123649194311770086366079669790607391987127098124722622123545919041487974676255540688800220466206610850454672997297419289949300852267384779877087053059761447959373500458150306346540860967672387458445621189336334711726) (y := 1551185265638900823182204269608782504649239250311690830980991748394972171664003009821915045166193555614346515963425391476922082389285176344338629800643791469178966487080765278772228952856400026552951359536824287400795244212473595679783354029407680079573946941252195466934306541678000517314042692505621737048579726982) (discrInv := 336516363784878221814901028069766852375413491010817992380496817693491422358307715046191531411557565505781118205892759459465762721038122289471949247262211258450672021037083117078521979294235102548280208840817893167125387196785699581597903519585735889606805537513526684208689254717857327890887632943276690821340381930) (inverses := []) repair1Step46 (by decide +kernel)

def repair2Nodes : List (ℕ × ℕ × List ℕ) := [
  (3, 2, [2]),
  (5, 2, [2, 2]),
  (7, 3, [2, 3]),
  (29, 2, [2, 2, 7]),
  (37, 2, [2, 2, 3, 3]),
  (59, 2, [2, 29]),
  (149, 2, [2, 2, 37]),
  (25033, 5, [2, 2, 2, 3, 7, 149]),
  (62659, 3, [2, 3, 3, 59, 59]),
  (20301517, 2, [2, 2, 3, 3, 3, 3, 62659]),
  (182954835021961, 13, [2, 2, 2, 3, 3, 5, 25033, 20301517])
]

private theorem repair2Base : Nat.Prime 182954835021961 := by
  apply sharedLucas repair2Nodes (by decide +kernel) (182954835021961, 13, [2, 2, 2, 3, 3, 5, 25033, 20301517])
  decide

private theorem repair2Step0 : Nat.Prime 20920785857602026591961 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 15498634706165794764800) (x := 1432688066402740502380) (y := 4028899240839007507124) (discrInv := 10750155183600409262573) (inverses := []) repair2Base (by decide +kernel)

private theorem repair2Step1 : Nat.Prime 149957849899275170552855922397 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 148011815986989589935492091542) (y := 25322448305382710509645481680) (discrInv := 111079888814277904113226609183) (inverses := []) repair2Step0 (by decide +kernel)

private theorem repair2Step2 : Nat.Prime 56613698191240130503234232186692787647 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 32688654290236141122176974295850645567) (x := 31014096506686176861391546401088426043) (y := 50765582691484999946599502508603009609) (discrInv := 17333828857244581638141831939378571260) (inverses := []) repair2Step1 (by decide +kernel)

private theorem repair2Step3 : Nat.Prime 278544886629625992368539020855535840809752773 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 205589223411432037211108542475298687638780346) (x := 6356135303599969036178362624754848204929710) (y := 233863230230823513971089360651450039678479997) (discrInv := 114415665663237931698434213294398489078111668) (inverses := []) repair2Step2 (by decide +kernel)

private theorem repair2Step4 : Nat.Prime 9652640775803870903907569183438840952707991359805630841 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 569021554828752638758344015311856813752728810884929447) (x := 9414435376397668350331693026554865114907512637496854119) (y := 7807236587690368818160614527965270535689636792085212124) (discrInv := 8570618975572724395758929261624866306977882032934597328) (inverses := []) repair2Step3 (by decide +kernel)

private theorem repair2Step5 : Nat.Prime 27538984133368443688848294880344183941704689385638881833243 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 27538984133368443688848294880344183941704689385635490738459) (b := 27538984133368443688848294880344183941704689307652744720667) (x := 6847251429073520730640062329244244776029768422689419959770) (y := 17660398038978765581783976451608235456515972337648562425678) (discrInv := 899276228547208104657262165874407219202578118645704055078) (inverses := []) repair2Step4 (by decide +kernel)

private theorem repair2Step6 : Nat.Prime 2506047556136528375685194834114082897754584944579138214356089 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 2068889417133476472030356100362085128630006922681169012668910) (x := 291377827777814380645314431966840737894368092991899379932628) (y := 2350708399072054231534393991804817358680036589428679436557720) (discrInv := 2258591672893600977478810032409259160397522739660041214783300) (inverses := []) repair2Step5 (by decide +kernel)

private theorem repair2Step7 : Nat.Prime 156893844924892777044035598335521614226288354241254278957014661333512279967859 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 156893844924892777044035598335521614226288354241254278957014661333512228299984) (b := 156893844924892777044035598335521614226288354241254278957014661333336505857109) (x := 149023664252884790495980575860409268838477064574618924323782441283609058424718) (y := 3132934196886195344243704480667337789142930531055663601914921547626502288164) (discrInv := 72640430721343077969537579229257723244527053829691954614788169404935489629043) (inverses := []) repair2Step6 (by decide +kernel)

private theorem repair2Step8 : Nat.Prime 22199006137456173058340147758279134536105453569550155395908846175583918369979010086407 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 22199006137456173058340147758279134536105453569550155395908846175583918369979010086406) (x := 2309767104369449719185147947006576841731678214606128912869199574077508073141831798743) (y := 19067893088788961173629890295658118146216314748208128065607936078158278652161050285285) (discrInv := 18910264487462665938586051794089633123349090077764947189107535631052967500352490073606) (inverses := []) repair2Step7 (by decide +kernel)

private theorem repair2Step9 : Nat.Prime 14673543056858530391562837668222507928365704897671094511192891450189247349911261068525947 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 5409171519748779397388038073680079485292003625762389842974838584754494871559405934504531) (x := 11133979941411510466326619537676867275525851713996932618247488564909112740885755827043716) (y := 5754340089212687107737703307024257121305754140500828040443881189442771085611851094894816) (discrInv := 2515891013114803522626985696376389957786570303748617995096769891093266765704283828370084) (inverses := []) repair2Step8 (by decide +kernel)

private theorem repair2Step10 : Nat.Prime 55598054642436971653631591924895082540577655842387012441459851821645382524616669165095101161 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 55598054642436971653631591924895082540577655842387012441253074142537054495916475145881789161) (b := 55598054642436971653631591924895082540541464591143703251126034958187288708838612695615677161) (x := 44364944553604955516718537278038434012052040153453309281507249113202217820643157497835207073) (y := 12196599407750104574654966874096766338790981544752450968363746835310904716838732432839143104) (discrInv := 47345312279090289595021885649008581885984056935320063107221309407666612373818989159248207421) (inverses := []) repair2Step9 (by decide +kernel)

private theorem repair2Step11 : Nat.Prime 17904853115105044788307171495085137276450168865134416466071255894920242282859711027052167772474829 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 16129532043486125626602397893288090251470354009936336476560727978900904665471260116754197553704193) (x := 10078656581169687884669065757921684794275103908569474126041493633706521836341158475201581967539341) (y := 11568456085007577645451603787501187564130129442764279288909272842840814916088588154494274600154235) (discrInv := 11720943831656203747855481934527926825541825246717348641450987001652846599676147937366808196171046) (inverses := []) repair2Step10 (by decide +kernel)

private theorem repair2Step12 : Nat.Prime 1412681917201975359299935810358919348837630583055422301819191804580350508172918539851833422808687614745769 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 948864508686119493180696228675783074793331801107403632403936308885773285091533770155549129782781103846765) (b := 0) (x := 54751677017395238134825361807365100549726601682546618723265205970600490070194710798823791656488796808348) (y := 1157181397910864069219977821314677279375721779720356068625354186015974005975321511901449632470810025146547) (discrInv := 115954352128963966529809895420784068511074695487004667353813873923644305770346192424071073256476627724751) (inverses := []) repair2Step11 (by decide +kernel)

private theorem repair2Step13 : Nat.Prime 605749530004703822215656675867042463265482968230666750494423034083474842847583333725112696553792763277844083647 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 13875270022512183326770025182099314496194409991233424946288653039637009537943798958026214166998351367468536296) (b := 55718008260866854624045895385821022362897094137931678952662702298637320393383179028277208909442364423976504703) (x := 250650949981293528926429866326679371567531052868839394556586504347097595817707501715764403970203092275144145351) (y := 235589910763578585873333014241428505787178778516739631072594097746258934475239526817240231721957853314275347986) (discrInv := 204542458047301701898628553897269973924193499685366471894542978330944421439903447930889982796525715969172911498) (inverses := []) repair2Step12 (by decide +kernel)

private theorem repair2Step14 : Nat.Prime 1817248590014111466646970027601127389796448904692000251561504685141452557689427301597317011464686050620593237109 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 560853133492003456139856071124265686533264650666260987113016123793270740772098417191011355645795178614051764578) (x := 190128225040649078640364480636555253936613889576567406123531063618934646888330640170940446730042556092522735623) (y := 1502063992078640936136927672261365349333632807495245222251227807340636298252499589461702915047490166286066499929) (discrInv := 615332246450165614530072829051390313455556943216416824721096898101812959254654790480401976289256542591832838767) (inverses := []) repair2Step13 (by decide +kernel)

private theorem repair2Step15 : Nat.Prime 202634121278113513199937039897691310726642831566586180050644983856971710267907993542047043798462966158244931736893701 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 82582124582286961049838512718255316483257708558388607493269624862039298820743117249605230993509190365087220668469616) (b := 84303301091785604642778008694769011095900344530674932383724956006615302765796813611924028316326266813505241655118532) (x := 112524350815324203648299428962715463619860224213876070465557548021879745133961612060851414220110786865806085135807611) (y := 142534680466432468840462070853488342575097239405834233196318999904140392552483530434437813573989153256397782627210062) (discrInv := 72518897040783859787709077651535199979124127805330153330484424150137359386689646427660444163663940660224623716695736) (inverses := []) repair2Step14 (by decide +kernel)

private theorem repair2Step16 : Nat.Prime 2120377459230007396454714093135121199774640444130988933150161411441836485270220171333406629212036423248133307256199055128736293 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2120377459230007396454714093135121199774640444130988933150161411441836485270220171333406629212036423248133307256199055128736292) (b := 0) (x := 500351185317636318835883623981929450565190304799312766606672105699981055984762489798231686859173150184972041017340133466185957) (y := 1113330491351734358479220677528144695942666602919521923158253253669493028750219121685638341569014688979972050623690061725949363) (discrInv := 530094364807501849113678523283780299943660111032747233287540352860459121317555042833351657303009105812033326814049763782184073) (inverses := []) repair2Step15 (by decide +kernel)

private theorem repair2Step17 : Nat.Prime 733650600893582559173331076224751935122025593669322170869955848306350698545214664343844900030066585728924533085501554880782507793 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 348376813438960128121719853247022499581267890858480161789273399703398492821184300600644123045794635332392263358886191741481229238) (b := 0) (x := 541258282355656186753265854047580388461528696651049241296678747080730848856481863061767550486894178445185968753820954327428793973) (y := 119115432814581166582147847298146449282531223941978389742853679442730723307123586952874421627622094425521649933413804082877807093) (discrInv := 384810390729471111835126793006788958619280340485099128220115953076545760097475789074547726683293696855342293237969517547658295027) (inverses := []) repair2Step16 (by decide +kernel)

private theorem repair2Step18 : Nat.Prime 224388116216986741076690412806684582191920027445436067202811516779505141373343960282955258256739341476237464235288440128354092209636908769 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1) (b := 0) (x := 198547245055136646207592333851452661124138318287361460560182853345112892233114466915482564332219447787733215846196862798636560381254591251) (y := 93632450179643181669857122168083672787498425635555599183497515765039793426358776403101540063440105283586810059402253779932516654257110231) (discrInv := 168291087162740055807517809605013436643940020584077050402108637584628856030007970212216443692554506107178098176466330096265569157227681577) (inverses := []) repair2Step17 (by decide +kernel)

private theorem repair2Step19 : Nat.Prime 39267920337972679688420822241169801883586004802951311760492015436413387564976841379459712933701105181954336247224439580211261316800335627641 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 27581799119850759504473173681127310464418164566864641090868010912658551797957077953421661595168782107943208267773713257617868073900175429574) (x := 550521156169421212057363509136997133656828527418546056788289491436960476990225850791361943865473220128684756774009003759600664024461640600) (y := 32339567988487598612814429818988874195747254719516727064427922668232626548798706829058472261482305005262639895680286250670899624829765073554) (discrInv := 35760629387701493405205603004315608940809337619920279898447343099873888127510107913952109229577337967745771086916751724865214005864514719456) (inverses := []) repair2Step18 (by decide +kernel)

private theorem repair2Step20 : Nat.Prime 246443711073338256010269410125349164655443937102945181244311308562077609609307333874863826891503377083709741999164938365154488622931432834600430200516219890473 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 246443711073338256010269410125349164655443937102945181244311308562077609609307333874863826891503377083709741999164938365154488622931432834600430200512828795689) (b := 246443711073338256010269410125349164655443937102945181244311308562077609609307333874863826891503377083709741999164938365154488622931432834600430122530082777897) (x := 1245247065024542790828839429310635818450511366773992336693376900620631404638772560945700856955240966159976397391256435225261774529762254930223219392802291819) (y := 12578331988830871439602715350560724488399502990184747788237103189007435450022226096352656320256727554530729566516473240704450322621551916293267853844905593013) (discrInv := 137682945421791985761530408022362418524241453716112275704108942332194490702033680296515989989718924185985355594861523134240202762887097911553616553656691302922) (inverses := []) repair2Step19 (by decide +kernel)

private theorem repair2Step21 : Nat.Prime 147905978507486505213532614551601537864223614679709688010211855039940246008169600817017863229598264409248314964342090077440286377776171057306610003346459153368918265653 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 67203389090320252359699754949512370147865293181016701817717613084371733636347386511707976670620072477622806261844196811526127184580290200495775436738294748090204193422) (b := 54940376740613814428923817548288608247022399058481867872885618801720804279146045500197858044567622859352710018468316955319772741181232001158705579756803497811832247964) (x := 78458465328260505671026310919476695011160275359611332662787375128366742735286837368497953562869885424367485507629216631604756491954364840834860195302564371946226220912) (y := 22408283250333923709404144240089041091894924417175425375296275892243712936950418944310737418890944742123033084860818567224095942285904562617069701265186962993042419338) (discrInv := 64301770654287133332214174459477221165745518811582665271822985695417076445079674897994038951963666987904462793579315781076654783044388365099552083801713278273823801446) (inverses := []) repair2Step20 (by decide +kernel)

private theorem repair2Step22 : Nat.Prime 3338237934913970422669431110429646709595526983321047658390481568251451352404387890440075978119432482824825370265986814355350558463037952350673354485786026925692286703238837 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2032250221584586623995248478751464283807166720386361592604772098895775677614176812466210819560588414896607587528989024439789319611996125587960539022995560474851128828397440) (b := 0) (x := 3194368167219802951987266925785395278054024013598118763396650416123256256225058149108873651541360715209036240686287605407473952958342111149498226005391007084821648569575513) (y := 1586774712885758015397876521315156834341326828560218555222928368097199332439390438270944477227999212908085826472182859096688043342170224441475758022492380099133294868076823) (discrInv := 508062555396146655998812119687866070951791680096590398151193024723943919403544203116552704890147103724151896882247256109947329902999031396990134755748890118712782207099360) (inverses := []) repair2Step21 (by decide +kernel)

private theorem repair2Step23 : Nat.Prime 16828544141029746928821344539023134977481319906465678925492927347258715707563227160158840742851694376849203714585091946605374273993069362772010031466514461962746977200015834095572571539 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 16828544141029746928821344539023134977481319906465678925492927347258715707563227160158840742851694376849203714585091946605374273993069362772010031466307684283638649171315640076359259539) (b := 16828544141029746928821344539023134977481319906465678925492927347258715707563227160158840742851694376849203714585091946605374273993033171520766722276180645099288883384237777626093147539) (x := 2214975726135565584781885042795543044648533742370565278603156786031583690921685862781335019684917258116331962179665383173030944794401117912233223466550531021218935632196319773894315109) (y := 15583630283860560122979734647209290297968042114494824128901765540958303867721144157192070102623165911759118313372476910865739013848818117301288723147781360144938977740505999323878624761) (discrInv := 84131548994812911404006587802527573781579986002750317652077670526505153211724341478210318269764839910600025143595931915858237728695443927632134023496987325724978592736599733119810167) (inverses := []) repair2Step22 (by decide +kernel)

private theorem repair2Step24 : Nat.Prime 3530136763414063452342470209314245306178999002283552885567497552146082266738927230450796305888419895415291160940370866473168405644401006280445184677769663610653032928685012764163955633514412303 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 754163536083469629699424425846478015975881154065382613503606472458311750732212154257596786701661198673682182378822424725093056269643182361537964202818580217525158481611277994977849658159640691) (b := 2216440064590021301583178270890749096956778820089037663015026032722874886912797798105729980737454619073198486925299946015096020853133726401628570711912641895713510017864153508512205917687837285) (x := 499588354515207996091277497006384481464393998885454312968793528630295795661721103150102523964979334990435812894579756307812981215612779365443837949381172657525899573927135442370426501589877043) (y := 2883825767841282355146604101447420970604320444070422473592463690743602934002470254603249274025783756684537616171131027369429269680955951119107493367697698216159379111764409893512002696334032278) (discrInv := 781663425592937670576286759890588964784529980798486323566422675086033800189119244536171735753434753038111941389153543775835917167357697576933232897692285265938469960755076517239992701044464200) (inverses := []) repair2Step23 (by decide +kernel)

private theorem repair2Step25 : Nat.Prime 33165055949845926228351323451393007115321482270617604857233406432813890938520476146019437363227539226969494041791498300888303561362279041745789248687036786650446437557358385443655653722737443630811979 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 23476004933408473626423027649347629314575028329956730392411746146123661735478218428421149023567518350016064562689291565518006860709199093335194438167438449641201240128737958705523241954110682221399639) (b := 2322262179986438347843649900744597973425121391920847272750089663539703055142596103537136767103084451651172540750341006765906971177574411318194300575071456679795808524006705474465897178442907783570676) (x := 22903744378989960816828895209219541292865342793645876082923748362602516226780244451104407536690393131990004000035127905253022843700877064130775220245316107301974618289683884374186279259651301955151351) (y := 27361783635431002966819173892402976701990603825695735209240451163903460959452731319093343677034975037722886320517799412200477054051342605647018883634262129586357100601845136783337909161276618762575020) (discrInv := 2712630804337709926239903655888399488855274304793326317928747046174406224753252656755255266120461568361723284495947969637441321104674397406400902749430904131772110852374868848848983767011056091895813) (inverses := []) repair2Step24 (by decide +kernel)

private theorem repair2Step26 : Nat.Prime 21830500297305018487773075816105970925933024538775684609721232126922988540473186808526399287212793145047073347019662618111215227389068171473994181984125026667600190986513426961794644976611985428157028942686261 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 8503031271843321763807170247048240158698440169173653281418086805473166826388179285425619837759975223420968858486718373811404296594061503252247653990124894435287218722138597953198766265041605597763746147223616) (b := 13123434748166145098927475624725894441727302387937299501694223302568865622717984326539990617063114277574802811660158401729857855251226733318886587270174875902065575023291169218445589297230023051409362631129616) (x := 21462670001780165624960789167485299426921689055123470734151031633375337123209594187571012885186667955937981829329747889575062960160462830550101457182599292076926247179114595129313406844969482637530638614026645) (y := 8119145868799709643975846678177394796927538177295575516413107293406856825321679005005983529463546706264346011251625717413362195479702575164072174157476594734831526125928432406065825061505676783309139413851587) (discrInv := 11632358992956527048786883246743333483271194967710152411908089188633595982769504262175297817097996177698483372194227577291457903487064577604198271478518364661337954651182654459072719409107477707250890827044927) (inverses := []) repair2Step25 (by decide +kernel)

private theorem repair2Step27 : Nat.Prime 12225080166490810353152922457019343718522493741714383381443889991076873582664984612774783600839164161226367748691421276670226478510314344065543879499554652940964489651402763477701803139853483892906330449131056701 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 9774452222915099689943329878717586778660073801869133323059741605325664285920861701806698442686075481041447203883190850449963596548728133211865447109399165799068225908934399921170440664937052366301572432059358014) (b := 4619485664535262011974875331263095774994525022031609283388746718682469367015631502457589605784930689763144913984577191489666051196326565471731210414478028085277631666393842719006723543755467023609028370884870737) (x := 7580418448035998983826694646092323673012314011362968162618529559519424494061701187917915462304603102103347174641656148146473353737327505734922138435153285800181772697733642918016459143730715655130368322328519598) (y := 262292505660375133985321574340677979076907928584704572466108665902262985142162650987219208390952621341126445542916382281456627199000031490001713359844866828252558287848810724936286873907850187644244965239445043) (discrInv := 10025767504459381176763971255964433473995461532878780460624581552340519707585615390105209778429151346135568238669567965032920078991305816181141864757841689304166325267677671633981954527313085506573173681696406119) (inverses := []) repair2Step26 (by decide +kernel)

private theorem repair2Step28 : Nat.Prime 286353333974346174931973464773265520275438772629472422557181019021469755136149645858376474988971304667322861549644679647268855373803394052933806584361509808919859379809953304809599150971468928301259103532561020658987509 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 272829319257766868570848661739923117467016396585064913263936611750892099185668319488423340229131594655859516945226579117988074152821360029102306779581077772524617559496955635512728973018379147678919532585915045078333480) (b := 77563774466446747066950039620327076950606309127125956174673972473249937890752633734609511368376351930924666919485688016671045443332401259782204500264658855064584347309729919620004643337657098493664154305203599471206410) (x := 227778527757293415240999088488514295798083308352759977479612908745824430058313450620553241435390770682549260297799571305814824663886385140617218275273618810475259631644758073774728995394278974762875445791392038126317830) (y := 114567313167613006566776525626325401624124185298540567885863391199586694361357625531249056178030014226796818331951569652309290212187718368465782343724784854372056588554152245096820319184281678926346569588078411916473503) (discrInv := 192308589470488144662044162705020325738167124486174839543581122944682394903283027490544656393397679922389683463768595907055300403116704803451553032955029132194713461494521929735970777156471309994092585261763264264044115) (inverses := []) repair2Step27 (by decide +kernel)

private theorem repair2Step29 : Nat.Prime 38084993418588041265952470814844314196633356759719832200105075529855477433107902899164071173533183520753940586487737359458818901804038968454106247167092416877041282506318946601507090692454527039768785493269482092231268087 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 9038324787947908336091598873388174531809928868763165027507669515764641668497194502803893852457063949412048548532623080742337591338217574041180068714204582806679009524645290011643995238595473964700168811589538506356901660) (x := 14083992737824528270745708471431864047935101597286916780115418251688940587067597848065227353831436519030393173447456435786333989038595434789407757554162215537743510806141212785323357068069820966300104269374973506055336035) (y := 10463954984391009562394407811127164871938283231547326901498237116805546722129818075208053467440277066216250888014314841762152626300184659041982321370923710461195098027498104024241124374526859263701981097201761048231430054) (discrInv := 657916240924019058311133891132515431513622597549258156894337466540464255815817645846942592056612885514830223753866762403030702769438273039349420123419931202235881446894374286575719136488703740313646699596831943812666409) (inverses := []) repair2Step28 (by decide +kernel)

private theorem repair2Step30 : Nat.Prime 162699244224181786640314019130898169625274486610950162038177683083844719016146693616840508709618454133394917201237889224886778066916946199210180108515468532191973006961170702121130124692308506101507638785061070379723525641846987 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 162699244224181786640314019130898169625274486610950162038177683083844719016146693616840508709618454133394917201237889224886778066916946199210180108515468532191973006961170702121130124692308506101507638785061068031445570082422987) (b := 162699244224181786640314019130898169625274486610950162038177683083844719016146693616840508709618454133394917201237889224886778066916946199210180108515468532191973006961170702121130124692308506101507637399987668303637019809398987) (x := 32488451048102836165427064304354360975621650504169083749658830058001946969513404118550993734805129879089726197254245480490232662407466126312215115198256920606837049878418663603986490383418503411279260867012197225683960599617594) (y := 64311545585544074640516871742911952541002043663412052851751451805280674586052831416729758930888207192976430269256800438564912679532322656275591099388263712042437414634618194571196814589010605640898328510541152728473170030032099) (discrInv := 128162781907089958962324750093009861529383923850792430562962188946601783329845651545452046170635052026842212205336072210934650956310280049860486860338951902676452217189827933053629727106517907314530317521015935994682965269738412) (inverses := []) repair2Step29 (by decide +kernel)

private theorem repair2Step31 : Nat.Prime 7962145677182071025154945650448374539858471775261142614994524430063505431783887921229315316577705338584519913329414796334064423282392301662399601396095984523597597452889679957379414067818183931237449880492941745137825927715313843852249 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2411532334376240006697730477984444231534600045898663629437181762468287367570223749040342314885842172206414260980725364960304330066131918907193370853398608674290422546967798378743242089054154570596621587854121316114137642814345785571961) (b := 2645582813041208333542003268088089764181128993975717554078143216521153712824894493767385993169241355400145084272359570305724622094248846172009490612001982071735680084248444643838461353431214019235632852833744815533170620530836313652219) (x := 3968689133845191291560683130892702617052056848998401177955790801405887927437601225296076784135873296863062835379394953860642740682341639384570541550701899400384187247343135610090406293354852574353407779991648408137797515091878073423151) (y := 6715052544768192342187975629374647872374807661512028029752417791295845381692662353258104359607397689205807460114313273305324653884606535620005857802633813634142465251294080643689735164094555344833127743883926904527150923000455156061245) (discrInv := 6842587346613852863864296723553288524798079991596339805194474624610905484792412603817022570322548306556520358159971194675796835546322622100379731943200638434662720313171017046752629402183131106292319629235877120465839352757924325016058) (inverses := []) repair2Step30 (by decide +kernel)

private theorem repair2Step32 : Nat.Prime 34618226141956413112616584386521473715915892371486454756331035270646045449790621846137201186701350882797420199067455736798391794415898211889701472563707710753187598073453061107652268070955481661618679169827458971330283978566056665775408600528723 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 6132354119694168280594850594364592416932490618109222849711096782510676105227038531881131429732934012589821975485337028330695308746464180331095232970710296244411201205783363717837902405101213261506811777301889376669276244908025734345463917538053) (x := 34145643800674443887489200900182962663725924838673565634097985148045261541769860782336993493870791357505958265587726428283324647226330657689761036771134755520833606561375059935456456079705980419373602416381136616691077866771541785639567573281774) (y := 1064836037781993103447833763392788511205546072952246567757526792098969552577857293211252249533627311364274992740778066942718041648561728218350175925909360141024175792196802588648484129478800744341440948312731583710113696017695885316200809685951) (discrInv := 31912841848594250327201720137770749422314369582525587030258157140185168629232698673175754042431799352399843502340992078950234798912837544313382532977958321227177721020263563196880980948620503872043396801009401405803186060236150059850273266327185) (inverses := []) repair2Step31 (by decide +kernel)

private theorem repair2Step33 : Nat.Prime 68609031553316008193980105797621632242204525109632089006658326858046901971849238461935011739094926482195019954447012905823049499383854067340973616840185766854177323405501083107849354183223365157508647567091627375640774594351195722157899284855102786399 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 68609031553316008193980105797621632242204525109632089006658326858046901971849238461935011739094926482195019954447012905823049499383854067340973616840185766854177323405501083107849354183223365157508647567091627375640774594351195722157899284855102786398) (x := 28549204752643084321493994121640824648592555965183465119787679903004092942978795480266196777248563953426962743522382850875692234467455028992621593865386234125424123810168391449954810375090705236521116569577040675290010273856366478483490733889009712594) (y := 7795765179568701657374923315369709711696108792026727044320733446033039833890156841294122723645118771690416722725011082940037223756796599726323945107359771431231842330248374419843934014478163551699105785732955562284357232687167830480504853106564031844) (discrInv := 20328601941723261687105216532628631775468007439890989335306170920902785769436811396128892367139237476205931838354670490614236888706327131063992182767462449438274762490518839439362771609843960046669228908767889592782451731659613547306044232549660084859) (inverses := []) repair2Step32 (by decide +kernel)

private theorem repair2Step34 : Nat.Prime 3476218421775437955911065794874439546858870231540245411215599066281734676228017247506730028026478138986629460562415515406738514203538543263336652294447486879192201371508362936150753394323477434053461714057467512705007301592036280938481533892530382107930531909063 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1915488636727621144121615956323991017005245516069796704411730500276185322170535742722330039044801424753697787962470842189937182342251465293288964352952801479079786106808147518495890176730408148757399194077986843856649597777721273085116873885785338914594430905713) (x := 2772541764786477336267737770436064442872222539125036453133142907614438618673880204792791657664808383398488366072807583081698033581212163607398695054886851657029202006351989537540232357875049981743720012377264876018211067931164102503545571265901339072537858136765) (y := 2804362988816519807787955986683006038114421842712770616347222845400627966425076666003771754686539456827214043450194408542032901231896633227552864987833609420171048735345074412138852014934927152752991073126753256559048938273919019417835290572449156117462982955426) (discrInv := 1991073365425417383690439877706536428773147861770671639327605733709471580712081583320533589639215693281107145931706588319204311856622541785412736634951891752567676778514455887322735900632951297566278475923807581962353160696335793193061083692992304114580138201393) (inverses := []) repair2Step33 (by decide +kernel)

private theorem repair2Step35 : Nat.Prime 57466360928838392624421219219886694238834385434478017402992675826036312508842754331466541018093725688335721788583011736026200705513757397504534793799587735814820711600343973689410870441814252243225818357731041293098861734797619105859452378439453837913586888549747275307 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 53455572840269425729796244289013418149617380833056902527386130967768852821586873401967165493421339799776212291345574408321564983710186659724971893480852886730746682512806776676728195718252397149834562054866781095982978185287318126553335159169987625992832377137606162471) (b := 15316032126721957243176874777350059735666913545921993541618885708365995869605623379332481578096395744686253770389895538201366471953809985089570489678886550778990598312149148020515297441173891479212618440501652177905861137214199694015576163722046414876684003786463797004) (x := 30938062048872867930985475310358173484367829904661540323475528573977625581571208155028188230315508985951744489795004894760462448302291561903235908699606447123098792001182335035741894810739721725953096295693394326481812075258450486544772076328451633060650859696702409121) (y := 22360030825445427146225141741123816430606734753616103981042825157290535796696326710321983847745955637570877900392008994264309827058842411169962565268660391837912163423578336033564110494614897588640772182677993828884103540322500083843231169285508346669713280830393482402) (discrInv := 44563105503801024819333605702450931463462705010386373016525378475353140835920081238185719332991461965243023147633422425495929266287116947513121550060066847528440920381560733088654099037803875233019035114753585043445603880731796176652803478456579061505766837446022316120) (inverses := []) repair2Step34 (by decide +kernel)

private theorem repair2Step36 : Nat.Prime 133302182440574858804533890564926897481886323136401290332857032177539760720119591580939512033570201184081362344452732115967640990207972999033651817281234175472840624157753927687175660900787290486723592855366907024262475847197081498437687783590471152544382159672044201926449173723503 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 3780341169160784815037949530801126415838778938181995482958642235497269178621694491502665299839485133863364323594491155411517236312083545235950081311085122039170997989473403284153593078623621907196960702059865788325072635172799416292580483632177452788516912136019808084696537541331) (b := 15507507060218504016943817883106940571253531002870135184337077535277638706557624086110139394403421913257906533557334356126165022578917663004885201233297288194289702040582098694597127293053577637276271545221896404521441377955543867298961416237167958153653799858321466156517901205456) (x := 7135968111304741758266908941927050826328177008148978630899634679900545223431417080398554198302344392841106543751670617929116752633450041507476949760955199301090866026083786325971307128623891607796533809505945366436736534280555745726975953433367479925577319265924685236870974093467) (y := 84620704171916875278859585555359418657615517998119489864492443020112651779228643347943841251884398601556831485400558375416011085130151883329745680146865929550350612879817353352899574211650979867995240236196942236687323408155842854762533804844400009629194268576033131715870960209135) (discrInv := 30916729615042670082425761381404252024862253168920144125683109296379120117067884596907676255158289334149779694567681192804620397982679145373574860354036398859520874307470406557892013489327319037170289835681408189373997316157138968940767289252890326243418907988624361097611584287189) (inverses := []) repair2Step35 (by decide +kernel)

private theorem repair2Step37 : Nat.Prime 83346922966604549317817206007939412796754459768388633978038193654942380310733334396799268019965701149944503643144381850044535593845554701699792578672639820123849220038726085726593219871347497894785338685750582887599533284134589323221686152017183787105137710129225000498152657278451262021 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 35368628804627606784447408628695527149599441029356457492365706225993131438305185285478013385625038028286936342017665119655162021966468091992820061785146820134789226463172622289762079659358620655105464778005045116039991567630667265178641782466700001326945083803431556635904168092200830176) (b := 31340363905966079067410547867661363227309589368205303196632170165783194044578060289458945989644381558211978469327765359288129946255892077596539436386230069710636317716870824270429271976719555703620819481363990299102282592133940360041350918362509618038064968434233961052066066797017106448) (x := 52350173046927871891753952364354535965740497233423804183080817478310856638229988317281662194315518205141724339059044544247570545980822015628964338200969082095584722434304510758850946767396984004160942625994726856336403819822148195789245141396500532636208269977056657975680354158105260923) (y := 38357586994022633275483271285956328204098585064430263525610116142428426828032222553825691909684067073797581013275136876164619533392446753751206676897300119012388974176922571813093876518422338376505280990828390690387326837914368787954939027641688122692973764913615094175610325703838770281) (discrInv := 71237586094009692999152438821030462761088171832420869589075683374597734903665654974968543151333765109529644092750841909602449893472249416595473856680765994450120565536664754342164653931445221554234799395803862610217675130020018625493928655540737039569727086189656959540970336063989304645) (inverses := []) repair2Step36 (by decide +kernel)

private theorem repair2Step38 : Nat.Prime 34627712039831234302294868577997397936651069044146325599513469960142119453505973278338520347881476425545289971825129953385797781047356827170757218265261183576187626856613637168410214876709647833906918934976437484835773606798841756359595428339142202392513682754774684029006724472626585593965308895713 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 22893813363689876634256919747215914272323027893947630668076986920297861274151655487094430832973280477588578324230956481899287588972009520637655086053557419572911878574744172469833523760884733658619161801973346232252310331765405007253389208934884869171058691111081569154084401628394365428997334481853) (b := 0) (x := 11497418916792730033263769732252495570797376661816497546378145126539294826680682125541302816200075144877230577216653882946151560692503828314644936606424271575707522376572151977419282646892048090347968100905487532388575995069787373063403083819632383486744884055870633024984174961315108205409153193174) (y := 3045593617068375526468879638613506018131729859550820374102559281524448181453597081889335665883928968726143022884096320920560288225448632738768812268292242647449770814083354294971904218194053031337305502752636972478499078270657495874718631765564025149949709936326434739236778339117129207266863091526) (discrInv := 10186209722603501550519065655699758872342041968575003989230058909683648294507269174816844768364098628881327651583870651261893506603431473217679063500776823037862513933674818661523832422393516268404475009815981294148361252862412086679465063259602522946660079781501825534959020558441320508921071337653) (inverses := []) repair2Step37 (by decide +kernel)

private theorem repair2Step39 : Nat.Prime 63262059679808478571548541302515006238426571058131805164263148539582840871999132701662209593951626911357201155326766414439581682151037134694799777193171209844077840380762838067215790750302426874940645281701211330157748846071743175819143114547821463689011630480210612703764064721286835784630591370612830557 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 63262059679808478571548541302515006238426571058131805164263148539582840871999132701662209593951626911357201155326766414439581682151037134694799777193171209844077840380762838067215790750302426874940645281701211330157748846071743175819143114547821463689011630480210612703764064721286835784630591370612830556) (b := 0) (x := 8573885651678689942890410909145711729285421201864295123901110520873061282586417163423913531601265652439080137731506065398933235928059611285185758734358144961556135184772288894746247668731610823016836282037224477124879971155279709648890273952376766355178435271354007084720338953603906453020213869587893331) (y := 12136655810704512982936721525671663963146377075661979196096747528900597933118412973217163857925461756214087898032323379985755550315958501165141454737114885822889105579369847898711858979230712954991851945173253444842955720645661727346920192349374339372825093464945793902136256004455392938355035559781198887) (discrInv := 15815514919952119642887135325628751559606642764532951291065787134895710217999783175415552398487906727839300288831691603609895420537759283673699944298292802461019460095190709516803947687575606718735161320425302832539437211517935793954785778636955365922252907620052653175941016180321708946157647842653207639) (inverses := []) repair2Step38 (by decide +kernel)

private theorem repair2Step40 : Nat.Prime 20380453145034042654040692253117283742436376145446332567375170909203908478228043807880416676451169897525514788580721389473862965385635395160751977095135184185447664208638272532589648712911143625141534863745196292832228915731963189095754096798288108173270475599463451393140802439348560211538846226110203573961871283 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 8050896520607356587376620167283776289607596064939968166785988351085472796157718284995243063222253633934817683691462160484668446068861011606452921997647780261914897862889222627204794258388285181156385751931226366793416897750083251116795711588976734820734698021612430902230437865719996942212308003187464346404871077) (b := 4970157310574568645889303243108603806313588631577668536136454973507120213136737021196281030712107534338874156384119743161072148614559227853427053910478746615514510273155587040150315751654525473086677215477115341532355885521558369045337024989945335399392517204703942889987681566090756826068363825799744705597310113) (x := 19291942095127758915287817794029130174277271917931327179775918767108615066392225968293085474051244818942797416123017189407618356675834123568876099133627848593016001368610228489078404095034230517628001755853923192802396517143068036084451294874463211305757145448740756347403232988986854141340731865757645570205075158) (y := 16257037984415895145782090036507006428941017312571008805279725709444308947205026752583945456950634433898676142947990171872818279049174757077968261904173698044273859116970459103398617581919192730373478249718389208644444519049982947244225763106835553125900680850505166062439366948222495143998017840442362943676936017) (discrInv := 12525803057644846540480537656592967404034091948335305373328293108314566516026902777459496585602271497785575066967321582073605857712434070622453307190823712707617091328558078920492575009777757987349570073586318280448815809501451068436844699042004150227316614157430306493362389957089975124285796553947279340314696017) (inverses := []) repair2Step39 (by decide +kernel)

private theorem repair2Step41 : Nat.Prime 3301633409495514909954592145004999966274692935562305875914777687291033173472943096876627501585089523399133395750076865094765800392472934016041820289411899837983078822971151287505329192256833700473564074653855769266476286466558649773813284743834429243103534273638709684354283822887237050730224948774727416205014424843 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 3301633409495514909954592145004999966274692935562305875914777687291033173472943096876627501585089523399133395750076865094765800392472934016041820289411899837983078822971151287505329192256833700473564074653855769266476286466558649773813284743834429243103534273638709684354283822887237050730224948774727416204863896843) (b := 629407744000) (x := 1574268371822670315182095301681583009079932509205542362145196835301294360868182743637743695488051907940462789160927960845067550595060863842795793227531057581613729755050825583152719385460947327001346427022624798556552280607700686138555057962837653446062353385016574835298189688274786679336621481442294572549938740901) (y := 1005719465047474803606652500339134612171059806206885396502224731869829300217387602094043106390274497476863264984316179419207489681944855959659175561281530268682632373368251712478450337450280162868162630685242962845595523674082533230499386117656040943485013002022701329737515207078609703824890197862054099744477069121) (discrInv := 6396442512024467312202585038630070338348788130073587529634880626790449940488624261696579983731268122417149506250597924569278343884164180013410802119458457285250770630532690316321003887382392539243757011870326848611543049740059457596595181962443965845671034394901739760416809194272766013125362115480139104668374184) (inverses := []) repair2Step40 (by decide +kernel)

def repair3Nodes : List (ℕ × ℕ × List ℕ) := [
  (3, 2, [2]),
  (5, 2, [2, 2]),
  (7, 3, [2, 3]),
  (11, 2, [2, 5]),
  (13, 2, [2, 2, 3]),
  (17, 3, [2, 2, 2, 2]),
  (23, 5, [2, 11]),
  (211, 2, [2, 3, 5, 7]),
  (251, 6, [2, 5, 5, 5]),
  (461, 2, [2, 2, 5, 23]),
  (613, 2, [2, 2, 3, 3, 17]),
  (2767, 3, [2, 3, 461]),
  (6131, 2, [2, 5, 613]),
  (12263, 5, [2, 6131]),
  (27431, 17, [2, 5, 13, 211]),
  (5584686232507, 2, [2, 3, 2767, 27431, 12263]),
  (8410537466155543, 3, [2, 3, 251, 5584686232507])
]

private theorem repair3Base : Nat.Prime 8410537466155543 := by
  apply sharedLucas repair3Nodes (by decide +kernel) (8410537466155543, 3, [2, 3, 251, 5584686232507])
  decide

private theorem repair3Step0 : Nat.Prime 10406627144225676597151 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 6919630980212683848723) (y := 2303837492315285856368) (discrInv := 10021196509254355241701) (inverses := []) repair3Base (by decide +kernel)

private theorem repair3Step1 : Nat.Prime 88055925339916451474445406783 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 72423774985694700482598334187) (y := 8101672850064175917891325526) (discrInv := 35874636249595591341440721282) (inverses := []) repair3Step0 (by decide +kernel)

private theorem repair3Step2 : Nat.Prime 26264291860511204840981821246012924543 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 26264291860511204840981821246012924542) (x := 7517779341737077245851702558164356099) (y := 10312159761431974515660643524519480419) (discrInv := 4863757751946519414996633564076467508) (inverses := []) repair3Step1 (by decide +kernel)

private theorem repair3Step3 : Nat.Prime 79482670913200338590864379667600161228011260639159097 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 46186536016934881560543526077027296951105437927922011) (b := 50100954027807934702194123129446205698219833647132525) (x := 57897397325649506876659205805390800908784381769471758) (y := 15913438244677697093941290474589871583515421248162748) (discrInv := 53143561502321088025536381333070505927237510145857381) (inverses := []) repair3Step2 (by decide +kernel)

private theorem repair3Step4 : Nat.Prime 22891009223001697514168941351582035984233950317145337449 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1) (b := 0) (x := 6852625761220921423781882385872937070400522404150698014) (y := 13912286293707121185116654089910029178365466506322468988) (discrInv := 17168256917251273135626706013686526988175462737859003087) (inverses := []) repair3Step3 (by decide +kernel)

private theorem repair3Step5 : Nat.Prime 32151818805268487262198642433730406851724514002441426429305227 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 9109646496567909406272471903111655363904498968790282385242610) (x := 24902642456381324330073690152377601323068290489073311006323931) (y := 23607010644790566235510555338098272542526457075995202802257676) (discrInv := 13175562228109191067074677845802120196823305506576229718423486) (inverses := []) repair3Step4 (by decide +kernel)

private theorem repair3Step6 : Nat.Prime 3043720699941165815970288328885254642389457499533727281767024587729147 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1845307902115756836135218023238227388416494039833654748208179826084744) (x := 2840441809281074809889780771663726151142583712117068236800141472698030) (y := 1193564691986413347305964926966776349289231454189603444992250952475804) (discrInv := 2466092465634571491355312225297715154272850226617375190996666503042503) (inverses := []) repair3Step5 (by decide +kernel)

private theorem repair3Step7 : Nat.Prime 109573945197881969374930379839869166712794591564583461574947652292577777 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 109573945197881969374930379839869166712794591564583461574947652142049777) (b := 629407744000) (x := 96075965921010118915514060560367365400089689436704387451431054304154128) (y := 16541635901581545467940911609544917277523361508521396601805050536083365) (discrInv := 64071606266450873920805012374304452721980039613588561984560098331197333) (inverses := []) repair3Step6 (by decide +kernel)

private theorem repair3Step8 : Nat.Prime 7528686559227366096674587893478838042125916449978953255585504595195324940451011083370873 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 7525608253998705053030350815335481085352229714848324110632296852459711349593232055997020) (b := 0) (x := 903035219871836099997818725457939447331490210761384107415591006019974419315518932117796) (y := 5323934284694287670039070749623940848410370714896036976972573707658065048200498997284535) (discrInv := 5647284495727689833417000189644967770787859021266872227927430382080397103052703069371618) (inverses := []) repair3Step7 (by decide +kernel)

private theorem repair3Step9 : Nat.Prime 1769964095328116859863808915405300908351634453708478162018131782275389229544256865696316687311 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1769964095328116859863808915405300908351634453708478162018131782275389229544256865696265019436) (b := 1769964095328116859863808915405300908351634453708478162018131782275389229544256865520542576561) (x := 976203497037858049407057356388707891395397546131515450946976882862458748605580180899436823069) (y := 29112427772524184139661865635182363154689198302473403650519130364238907902987607783098566714) (discrInv := 142509019605365174695353467647865379471946662502823135347802346036519894544877841644224812945) (inverses := []) repair3Step8 (by decide +kernel)

private theorem repair3Step10 : Nat.Prime 292736131690412575569735220327798122533185173933270339127221510699094452682880993524540682777942053 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 112466097245130384575941860185743854700844342307995337282995333493335037608540464641352489458896324) (x := 186500665214116441091012460495806183636014359589189610303892145418674990814407325764035320104879156) (y := 219351519651444052671132930099553686870619779006491580764969743152657070974574482682221486619967367) (discrInv := 180109836496963219899919586399146543890464014484423032580386131177549254093592643496426180101718951) (inverses := []) repair3Step9 (by decide +kernel)

private theorem repair3Step11 : Nat.Prime 727789153899567819291028485105378908115226185211113294050019857886667738583619927505346310788976310316803 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 517361404928402119557077773363140299723826824510697502195158393244737097603984570230638292315286764400513) (b := 358319434064593786439922919943470142971342685509888752278961425512174957568232968945623272269319969963705) (x := 523908132576455262596489030785528806525505829431139954168255066596020764529813638928809188301220131237453) (y := 368174787437945127668253642649155048910659181874844511318621186031780112965568825454712407852208169121782) (discrInv := 264576771085914557780395721449218029694530518686414489315054197284306802369426131613246983784090664569743) (inverses := []) repair3Step10 (by decide +kernel)

private theorem repair3Step12 : Nat.Prime 3083642645072468850336087691391490433684213346739487029571681596465756942675564277672325801032663997388379711 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 2288762016692764033858163929030340820256444036419890960016689652521076886680065163506127825322870502632897216) (x := 1506111025775392342279338641005749948108775778045669712990033976451107048062997611146380208807950248438041494) (y := 1490479594786162534952187736519711850912421517570878958534133746287271482778486648292210484976058135411666902) (discrInv := 55446582157003235657223192578086172907165448697269003783662153542034249989868713873772270976299901339336700) (inverses := []) repair3Step11 (by decide +kernel)

private theorem repair3Step13 : Nat.Prime 749391763716855050553183668110179817000291647641474429051552823158545346507049185646918415684647078346170224658085540720441 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 97418425283256272777844526113812644955985110785382446316885627848883037702210460092079996571711946646275580058051958504715) (b := 678571214826011478947690627062317107545573568266223325133847194308828938793180516430555481361730851532675839781753905142179) (x := 86708835053254556179389237004802545983778303317697495268133660893659406477386334443287297134146339404977347458917718326197) (y := 249846729055159727388120739881985580787778182042850219664238378508185288236849995632600819460082218359202257002716859929166) (discrInv := 341610423973667005450875811050337453917534786480193877040610677101116559314762496337315801140468086628332958905998581775681) (inverses := []) repair3Step12 (by decide +kernel)

private theorem repair3Step14 : Nat.Prime 169362538600009241425019508992900638642065912366973220965650937620003150049469487177799904467361821285171866127197581598026257 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 133011953596725716170587218688277608989480986006393415831351075654305675911008825198395553695665723995603696112865880162065212) (b := 0) (x := 89285719031179512040511413197026035080881593701118189683975237825312419589235477246410813614773958328272294327055163362051066) (y := 99443042261787684063877644833206682950509120569935456724340314594577747688753712362296461747196496864343321036945541092192735) (discrInv := 23794452983414634961717296837196508285830407927763403787398895854253515827634999422087493444680762257863595506954853567820123) (inverses := []) repair3Step13 (by decide +kernel)

private theorem repair3Step15 : Nat.Prime 5396445311472748062076029920425275089628411375940681024237522345047772509351498289269318644011804705405457416352400054179134458285739 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 5258936153454114304803826531469658797330860395704951239438809688646219106550815075940523000959464850546409038332579536638310105388250) (y := 4311045466013566671477631344285394719643409695305263459339165719690492378373398133573877573645775440214146199744143418394645809436869) (discrInv := 999341724346805196680746281560236127708965069618644634118059693527365279509536720235059008150334204704714336361555565588728603386248) (inverses := []) repair3Step14 (by decide +kernel)

private theorem repair3Step16 : Nat.Prime 226807481870650361916461426877469934831280094075030954182428733921620492577618380389304668787405115701494330452754621387938724992842601430216770037889 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 177072835694221120762511228721460434093963550076644065309622619601838812083494594162010592665667707261952093959422785207802627503365536193381449511957) (b := 50677070584805063835055161847097530125868962639558339633398029779734374250352565170262195483677268317449069198791596296879501651963143318409592063421) (x := 1163626056182104444834764785284093380689071477502694179622933456711327899067514065637218667110625174349324187080314361270417025744164763729551586090) (y := 207856807957084907379462881654396245792484873844990710535568372575615936473317890519617507346449611550675733244062834113739304721001430365475330445906) (discrInv := 99545505192342083923412581046733979305932680491095181234623765285016883493706835937414659465222756226872971447958129912517514193100764595495976257257) (inverses := []) repair3Step15 (by decide +kernel)

private theorem repair3Step17 : Nat.Prime 69038836636534746265199359572940583343032672955874972267406212033337748217672006955400313193873058933732743628337316531325098446819164617034996153239456009 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 46457425787983031851920573823780430332293335091978369469635254394174438459404646527104552333043331477532607792754538606336295595780654528144119355494599899) (b := 0) (x := 3434034003360122925542980739952283841421149336575314864383457622802488534069202942678597454239345687306230085237593169005176225263585553174004235365714426) (y := 15621799484237315424817675634804304585170797569606125472382439383625340781719030067721692531741112441181708471811821740269637731839114459573690079793703653) (discrInv := 40164771030405301735919376223760329924201170943911636833145845426459701548402843584774096812143961330916405773064352746909749936169209830740217276055942032) (inverses := []) repair3Step16 (by decide +kernel)

private theorem repair3Step18 : Nat.Prime 13203987181135308394488848560459172170186390717288456652960611709737298715804036225206257470769938401152697386335506007811659017684433605097012467626049377581176274864304991 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 10644487639353134464157056874317978248384311120091319867800490302250175497763271216447458785632312256839440295796979842969752043681358682418760171712181412616013624208254756) (b := 5896669483077766814803859783409982458180464175620435269135158272924440694801909094096859975403853377900858499637768722324987788827023572087469089944132624830916268687532753) (x := 11630528799608507104852825010538740597001457981809086169803277310382287385486749005706378915206570996748630250179339781809006986231949126046775509544865514726669669837013373) (y := 12582523770393037200169559126115574183930501415827323133185717415706548930302285054166660046415646828071861432509552491003414524084242302062854325156956793545711412267343546) (discrInv := 7139404281269523471451668165020879963147765204128973308090952955272404143627256349825685109716897418189919926280556453568301841266476528997128593278829463923586265521956769) (inverses := []) repair3Step17 (by decide +kernel)

private theorem repair3Step19 : Nat.Prime 5504853676723654990101680962995298064682463183812391676333264607551189021422567805826088570726313773570560029028185944286807352084606842184248383573346548165666044332657473318395137381 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2352859840512) (b := 3908407450990371155683513391012818740916029989840763789446172388882901787733287523856431344420034467229488937209760174500796551356554923704853689388933134319861454922527093416655556604) (x := 1439556164401132695332384178912857889506955950454869638707591003251305190461289348084660462822747205760606084755129873763696927730534241115080952864496031947782607508899375426006289833) (y := 3133484302781921682733236756315176793770743177909087099858668661555889838659986373775920242316361036554773467298781154380241048670795136983385437881107461437532507592843493220550924263) (discrInv := 4011405418496554536700162741567590677585901833288100209195063715720211317251874518648897844050702831248940735314196940032581933136534032301303151240648932865555782595574021846484357576) (inverses := []) repair3Step18 (by decide +kernel)

private theorem repair3Step20 : Nat.Prime 88811929240101941286136598224854859862575145975234266497471622553761847241572555522565335781715324553388744201217093819614176545669095237893961091719817695530858620837662330172866768595136197 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 81325576167927422662367780287683355177387804154857286867528020491328248134336641093114271515032491671615895780390988127331937257105383576402852526645395058555274055407541034041182633959493037) (b := 0) (x := 59879339127753165862417708331277880488481199330143809978214234130150073336225196848869149139968226822101152299610742412970041987433500149986555679048358833975723591283363552350933194474952682) (y := 24261058385808631949583488142109025715881673883115925321454176562969969083091327623003403300750512258284981395710722984840557091507882125396414013990062718554414126789936906680404104610677507) (discrInv := 86940340972058311630194393740561983691278310520140021589985722038153447464763576915202569715044616332945532096010567396543616723528167322521183950451212036286962479480132006139945734936225407) (inverses := []) repair3Step19 (by decide +kernel)

private theorem repair3Step21 : Nat.Prime 621683504680713589002956187573984019038026021826639865482301357876332930691007888657957350472008716840828940752800573486401878352744295949541972528010834706614256816145552654668310020156860143 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 350588944315667887944160478046547861064452320168394354204242718222179391414632239782892820878765560977403963021692881806320327428312289037016170196659740516803742390816848636851326621584976643) (x := 426294665460454343577122101992907397143145119412699861778041785541971800241147771525420247198642311038579872832610652055523119832582807669036868495512776172834941243869450916529306980348026890) (y := 462143266545390745547242588920268259139404839330177830642192985830157260591670907607416075978786375494174787009925450633628691145531474505369456518497062844803611811246614657261570330866985796) (discrInv := 401644998716165990028295059927289724810714933909431493202816659054053417176284283348185332624075656728204416746730216975437820279536005453914042499179608071350669955294952680518971687992564820) (inverses := []) repair3Step20 (by decide +kernel)

private theorem repair3Step22 : Nat.Prime 835246708942651043951607708954149305194044872948614498632243449539442324373705682601293491335555038163899363145369241830391267871802878535448081921181033934048693953474751784191316766456568175859883 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 835246708942651043951607708954149305194044872948614498632243449539442324373705682601293491335555038163899363145369241830391267871802878535448081921181033934048693953474751784191316766456568175859882) (x := 831749405785240079124441326594033488683611659541685161959131645241209390770057053406899457717932686679848729591925267626470925258397920914501280073234538022699413790205923644960627601497136568165077) (y := 146626931611029459002270342368249942863150240228902631815226186735772119554832962781698529001781410273216831618644590979458351688263613456120444640950809738838942021093338401381767221309799968891801) (discrInv := 618701265883445217741931636262332818662255461443418147134995147806994314350893098223180363952262991232518046774347586541030568793928058174405986608282247358554588113685001321623197604782643093229543) (inverses := []) repair3Step21 (by decide +kernel)

private theorem repair3Step23 : Nat.Prime 83524670894265104395160770895414930519404487294861449863224344953944232437370568260129349133555503827599521301042888141662660080582183342903451663893525340948074583559279035425324374496303389495028781 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 11637893592433475077804901950847411368717576781880960481178092570016625096887632161930554881578513089287796719312801782441125976441981269902404059272379106800031296240998892584116212010679820584503629) (x := 55593094886072418105608372468626791925749231817136099509092392843707620344623747524590783103609565347137460752743735501559668523418739497213248351757456264906399350590224105635937770097032659135129304) (y := 41950055494505829347686498075629126794396413556007663572418476848321586966031559232166851735621577892376314999632022922755990417361453744326268955450669088548163606086075515682161315867963403791476139) (discrInv := 12374025317668904354838632725246656373245109228868362942699902956139886287017861964463607279045259826311040192747094539505579271197360495244955802058300050510825864231004301544492499925378279925189449) (inverses := []) repair3Step22 (by decide +kernel)

private theorem repair3Step24 : Nat.Prime 7517220380483859395564469380587343746746403856537530487690191045854980919363351143411641422019995344595858867058354273520235156724042915324454502137371241921657571709021769392813720060861876516296187129 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1642562744203800535507277916656951229578099037227490816305635119546535612295390361493120249818497525282145906243831683331335693142528189028762672100622724778898825601328662502036066262522720432747343362) (b := 0) (x := 3442457819588752948551997426836370404305568862902051560796995061783128626966466475529487047261706870891538264908723792709127910248824414303689388483382880106566097303577261777831740386959413505108102870) (y := 6244042154617747751073345088746111067363404306337009760882195956225299168989826843487896021028631875773927110907706775335763095451885802097175685141227806962603507819169026212546984096313413871599990739) (discrInv := 3347969504190979563905415211129434065978677168961892539768686743040856556607827981332540648555373290977392956968219215927283655076389410405036583043529939766104079454178719070897843464800258149961257724) (inverses := []) repair3Step23 (by decide +kernel)

private theorem repair3Step25 : Nat.Prime 30068881521935437582257877522349374986985615426150121950760764183419923677453404573646565688079981378556086281498150431371783101332031866094203407022708798405191838611341920585857824884175130711360933009 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 24488830320771915783104891071172106271161261031690880441291100376124025148272496873773472458002277656912739787840011770358610901330146038418461125856729701389899695729624851256123508468029886242551198650) (b := 22207821564215436195197692882010918329353370836613962578762148167375584483107743918503712102010375947681571005428783575736021294099710038933316022875383436527679946605998229226317234910909023898408904882) (x := 10894510434162530605114262279442766081756458720836942517197416658321888284458690177104114150185821696501044548432097599571962997795455883464341697448816233240447953898617890969187550548605584604354806564) (y := 17843194106328107412014925416990550844819869294308498260372332006290151819327090525083529719652478240440509718753162442679370599566152810512004194693958381715942278861107637459196674179244389517119587895) (discrInv := 6656447941009844884638862285339665530995111272433839230898991822295434818642543759751459679178437212388561897514856739662355420976773250313691420086367502410216356161785193802450660878041296212613628374) (inverses := []) repair3Step24 (by decide +kernel)

private theorem repair3Step26 : Nat.Prime 1894339535881932567682246283908010624180093771847457682897928143555455191679564488139733638349038826851719087789447516129485716214037835960710189868840919439869208186124975510248424348168648386715985894257 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 138154477106810207295555220266790323899151274078339364615678733107911062695846614144642578677647938481796237033683715682588374014091560285455644017935419795733529361725492745085803407087653774912065369748) (x := 54101706536008574281382141641533969522107011258116910651653466592999019186461948180669332654626514228991594872562736924588300071949076950007344850457292980842544457584019792360382363630687385904412619267) (y := 1026034839245091176835750506357216855465778325015423029567693275721096048712381585420185685014707549275241583566586531591037925344785977733455216459038174715018465134320083830654142487143626599001223187894) (discrInv := 1793454648911089678940098459590866361784981043776754963188104732020738871378864393590544828782552620228282707297198491324416111391336657946464342443952126310515026807218772130828708727806196183777546729052) (inverses := []) repair3Step25 (by decide +kernel)

private theorem repair3Step27 : Nat.Prime 46999883107460553858656325531809210180523968923155246449151611549559946881105259297109771774293512237389800709050004860034992577263783975262570092730365063986410806043816196350106932970123725287017922324025122126288763 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 46999883107460553858656325531809210180523968923155246449151611549559946881105259297109771774293512237389800709050004860034992577263783975262570092730365063986410806043816196350106932970123725287017922324022769266448251) (b := 1390483697106419712) (x := 22142603532618762665789455713741602846659138266564150066088795499153879486897566598118224056302300895571315677428894777913934879671595255831614299376338313511502899601885990930771864349787455821158879664029376863575522) (y := 3202115201287729434866245514288014680615593180841974084327929582590326027520552921242054315490000209068526104061673755414810916249955587075400343071969271501672139534703268673541596773623932465239136674459535332547233) (discrInv := 4288926766856231869155206901400099009894926683170380420348391611865382824360317096082170520172057697138822086972767948839610666532167783531599638364114052770474668180914873122802461825324434700865640922958950822377603) (inverses := []) repair3Step26 (by decide +kernel)

private theorem repair3Step28 : Nat.Prime 4477283704422560161884090647538917380747215294434347998078692372491608919981663872266844981804747967167854451869804613221966097116937003249054935883113241505240123791953534100090710717382816258072466832297918995112753444694241289 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 4477283704422560161884090647538917380747215294434347998078692372491608919981663872266844981804747967167854451869804613221966097116937003249054935883113241505240123791953534100090710717382816258072466832297918995112753444543713289) (b := 629407744000) (x := 3428862319998952149537562281771189050676323153477844722222241028135762755942603308710953240737200443989778317261349301165573915970351725921452297378002075261467188805376340755511078897740742347112173472381759372951913360797559418) (y := 3090069434997442807970952148707322490891378743517790989506090483419636722967471029967974739588623499029956977732952244934133925683591338898910464158682474411198886556027949232795939047286720547174076218480021715221578559621838528) (discrInv := 2520574947729575618184488929138305736919741791163133723700183002640170128197668372088130332944994506623271998077600611209443176193010297821381305587025768428412128599523487256663910489019051336424412062942584506488064758907314219) (inverses := []) repair3Step27 (by decide +kernel)

private theorem repair3Step29 : Nat.Prime 2811734166377367781663208926654440115109251204904770542793418809924730401748484911783578648573381723381412595774237375502394978954268188640075967141409645817636614321534358138473697328797902832990827865940305603080501765471130927661 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1) (b := 0) (x := 2367422514388293552292738905555401759274357887409517834303581653912011298527471091662161697660353106092838687873374692771579833052587348077815057485707087162849500226898659383484660022590519122739985662463315472945253556450653736352) (y := 20334603791483364534428325404818670598248847922283399225889653068780442579221302239118036030635231512891648818705857828495969196011796794512384849956112625751772326560400196100821191175167676116224205850705487958898757796042277686) (discrInv := 2108800624783025836247406694990830086331938403678577907095064107443547801311363683837683986430036292536059446830678031626796234215701141480056975356057234363227460741150768603855272996598427124743120899455229202310376324103348195746) (inverses := []) repair3Step28 (by decide +kernel)

private theorem repair3Step30 : Nat.Prime 738237675787376175282365482946683178862624559354976934633668869058597515361475204498249275654832811764130165496100668339467348239892006147145767045273722291899022104518409501135142500494351161151140132139918404649637888651929024255122271 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 651911224195917827810016374450987169051995665281336963245653907800637117997147439855634537871598134039970380406315496072113709310562030435446716288941567001791936404149351895726217449637974431398561511648902948857030381271412541364735379) (b := 459854940882349230926879176089726851695923054941092521918355060996472833283730651900305248488018870791593683556500196880862525105671690706432281403347162942504469377467987737236725144541392289128265195329229098123054867279573597892152981) (x := 314417123920759126982651415715311879040230015975702386082004543121489931804526353858781803308000099128590981267270479228813441046317549529752584901944182178552785827215715669245969273516666151302266156074029102365562825485856300045351723) (y := 27094110159309919898329969295428390175327349159468774854085366567848920082665089297116070148075910411249589676578593366249858765581929380447617652012448915647586720080809602988960730843417229905847832988583967774890355389243472214310775) (discrInv := 638095954869168468397538825889573936704875391109653947897043303771658295022179922560103794900987208886819984848335628942134757710722758150528006286565130271393658486821407198462661696112748856658804660206944048700513755845061631886433796) (inverses := []) repair3Step29 (by decide +kernel)

private theorem repair3Step31 : Nat.Prime 11811802812598018804517847727146930861801992949679630954138701904937560245783603271971988410477324988226082647937610693449109938155973484321707646931962756462166771706957466522531334098659126939110247794797508426675580904437335424941335241 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 10551760047640019954580486757048139181352153658277002089820330015536421432000272928552068616485883680562086651913195807709895547225342145183788855633479310507743759412597221946672321905122793833032277637752520090785752386041020614870982218) (b := 1759769704193506331707935381714053033451576207769443813087841268756228964598271095295347927177800096815034082990890176090467597434077101146674386689507877808263842825584090849122584043137807032397993141896453350993997859350507841153005289) (x := 1732989657079926254233451748807808641864096976273051646348289249669845773067220050341942993048369954228048190410796376086250339558820731471658468215535442719143777399347144600156658832567318092856145646812645824095126276549749442127813234) (y := 6666151001952271774432230947967302084694143270453805741049907851627692191029643158511944447795521134165514652485957933365792541122557365930512658906723311447008099496220132999112824343095340152912503257414772168756726637243357829276263068) (discrInv := 129649874858945307232503726762232712477409544199484464892187159363142109892830345773143377380112187446100973156255318045493997623507643266491763071531964095080285823470415266470560126375871992917161296640837442263640661176472989577608485) (inverses := []) repair3Step30 (by decide +kernel)

private theorem repair3Step32 : Nat.Prime 94494422500784150436142781817175446894415943597437047633109615239500481966268826175775907283818599905808661183500885546985488626203235465208007858017262872332202146921227468527413155891405971112588819680598506887532471233365295741596259353 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 81055661960121759546336253957379596823375367478596012826931901447919140467613933466481593437566324435163780200301691802408459477812985074687788112482064635612986410986926246581403249253789267035915198746606627843748030090602700776187049370) (b := 87228726808467204002417361240120607458685036661335995669677867235677356702815415325064889224071842151649713388827328343320909424726996619949887880529157449125741286122709581556848537539735853561495487945241345680396156458628845197244032472) (x := 92682774952217674178965236844053334337297161741982081215386681647634544424879194813526114408379448108335661431056928485905168770532257072893640634661488666296033902833181747828872309266374430506934047377980199031512679272573023061582701301) (y := 72737332395851550700192626955491584379919576638459801824293659040237469146020816975147978938910931016758441102398772368033861049416109371003056258862652069247332147529994641249686044690358972242430474639770282350951487714192083341529093661) (discrInv := 53770514589920174679456190017284306947482392501538934157191222507235812309547060825508354656914654477254417791203052825720138462601127753809163779400110309125539832908107018300112129943763898444601290580156683200902317911960836279604461770) (inverses := []) repair3Step31 (by decide +kernel)

private theorem repair3Step33 : Nat.Prime 4630226702538423371370996309041596897826381236274415334022371146735523616347172482613019456907111395384624397991543391805262911902107989098436346265724558174304423671551977683429903386685543854612990405638434832295491946208375194988121543903 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1738944169873395797494853914579901707210139963093676909482405153658122486764543628276152518210626046085590704150464819114973872330680444741074804232547185927937086866177711625550162286561109273931390881432474211551823084339098760640942242665) (b := 725785610599626403619989878742223760792353318243043570832672278788290488020521602691610665827497755934710015046487098887179727674633572736320417758863440273034493838901162953552650036505627783105721236843710812240597609722383514436993763335) (x := 2037017944993217608962180533458309058839805063945245214990783605339055174317201807599898572560714000695651767019034644815345244685111175186936657464881534113021483172514406507614272751068213965666134978265210575947982661969236045291432434599) (y := 2950705182359622702722092343069317866827973511699680515689344757009274642620256085675628479194157671504845449810982251996342498530864528628902803152303781764530830160823148569701874462320448049757558365641258606740001326216299781686580979475) (discrInv := 3047261253144532064930614349309713658070201165710660593654166093057944479460675909631825345571538224962095666695776109949267389268120135629567819873100219043273301578349967825151531609452134819916439018423202799058337727924541062943545885237) (inverses := []) repair3Step32 (by decide +kernel)

private theorem repair3Step34 : Nat.Prime 16617883635410401479850505753150291266298882256988876633806290045633794259070002040098126830839622798035416964391649233189222204968569501968997088111051265191562396312593868504042501330048007295530469276650089932587294794203515404345407319991363 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1708478207464604698643423751784289666140896397480612962183117586861216090091879307099436470402799603042154533772672077887726708592005043818412088436899370470499581959149047077288491861321609112558558014584396603409595082511836536210647042561464) (b := 12102593212876761588804280463527084337515724671845819712715853247568793316376790948722574685768722767046119340228290895823816811645289805451780419970016211369306778595284599760179703884165471301505788454320867806686608157747768777866784436774510) (x := 1505099829743104694905424284387747310896650375761098858309951440236327347771016307428019169764072128900673586825537800534629847060518795371480513731193888078008742856576226261897818814995850975315159200735089201490144811636588171862337681768424) (y := 15091850631237809251810607246924789537875787240915935401658008939270846621202020974430195146134993228021612663924438227262127914559911692061311138678852751045373487744205292642931855891104403105728520157376407901834163554476302069611551055542573) (discrInv := 3254959955543229956962376795953271493161274224882346515887998374886539157258953524361861393296330614911843422161375631474384295661689728528049814649332634218813863779349680710314199451726635016148045160378162960975262901579536402530462023604920) (inverses := []) repair3Step33 (by decide +kernel)

private theorem repair3Step35 : Nat.Prime 4586535883373270808438739587869480389498491502928929950930536052594927215503320563067083005311735892257775082172095188360226723843570825400981524364858230609279448664908699588880285358642015345242304567347541512793095790067920622728633736873833399 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1433093264948306329063164204309804146492229056365632093117467016293650292528193642908014986076597517166739722059193320529372902952754039214078084733330687082522527673172194961939664739656679846118260683705633477281739542231080859021224327434161495) (b := 37606177508849257221108699743926965436321280209842931326195908568416581179075608500360209711152336924639479924528275224784582979863927048621206264385850956217030087620242273441782082567525039407509734477148399516995983818445734674840824980027387) (x := 2034490709709298936435126997938428603030510828517989871103340123766080151011206003252873289111509777895821845454875767191044706758049565083240519538098838939232010567657026143782012375714905062562417632856734364025323326377382136729992006015876880) (y := 649007001311826271818420639287798761169018928418519689918823395456802007556111663228560338749261155735016045879791344448673039267819643024394756240908280283900892005836310130236571953097816269559956897010845052357161799870881500336232326962602447) (discrInv := 3852396683289668544609109481630554391322493852990954424543217606973058691064130271306024969026234723447103256289371860934650299910038450911121681303856684614304150469141364074242449874882892891573567481511874079981537455828023200117211591573773021) (inverses := []) repair3Step34 (by decide +kernel)

private theorem repair3Step36 : Nat.Prime 817724309574853705894926003642073919682907053074193063091503411745044383397656016548104094851018768758854203850298506942368100754890887180665717274367523405051213946360830501046722551600007306831301858398128484934688853288517892251806864657181837092157 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2348277955559424000) (b := 27434739571737236032064870931393668279525256284322274183580777325286469971553178068098523425234997872133189309198849316657795414620789694177939662991101427058807600365323061920008074432465947577214517961975150546401319431884222299036783417019671420523) (x := 418760731536801233957899363581099269917191444025792571845417931823957799767359073329082653738678364451293218544775846112420367125564463519956790630443654034448053498800047579402109464652934652271568083712832909708331167910955544306802527311249518126612) (y := 9159125732964974797739306703420900397786928868408806701504296881955388794553902151171479884686148672552545951728130954161226178925788516150554347787816397217651512612929125539072966927893640307105573066278555122713232770851501091970684071262207056362) (discrInv := 295758949016487282056394851021072141409275238158355272433972071964870649086488792171173646076951276730956180919348523484586394416864848100655038877144304259064607201191892147866590112903172158193615470133873907786845659479990318592321463737359352441600) (inverses := []) repair3Step35 (by decide +kernel)

private theorem repair3Step37 : Nat.Prime 1635448619149707411789852007284147839365814106148386126183006823490088766795312033096208189702037537517708407700597013884736203596088216031963862445876019862272314499354692636785587115668121811846033315774689357523415882611683161675178635269463592572207 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1152852613256964679542331831476180142186351702844319153792227595104250342406995214743496567708680563538837394691913985198897973186515351919409720366620670626631853882747682778929757915078833527245325157877707476653623579575240117689949668428808006895452) (b := 749057282676573401742412604548537550182454378671164073369948605623437600565103462725926646898454402188671930816105911198491029667834870668343825681891248098626618299272781045195087574338288034158668803071214626962783041677990439264693766087791771254643) (x := 52274665647091783441654149026332476751259434949786099913551118046330160754581632353442134934027838945040896236473788991622617293687039414675668910262463792576827295671111268896097495384422983116221257035266289224892276031757414225488601583711077324281) (y := 1506433457762584431851281675139497452529497396812048801080518661539305404835409272844742461854967366206595910016593982443398768501981539843392595228962052395730194852634406186591531786624846395818148734922226091762258094892737734516336964203335294195717) (discrInv := 1575198589072881086735831549380493336537050536964407723865868229034317829311676786587471279683116363471956471001648229843216793039196607536253040344499606534194279754504828732810581083040529722286045269480425867273221974121681142984652581771837666720093) (inverses := []) repair3Step36 (by decide +kernel)

private theorem repair3Step38 : Nat.Prime 58876150289389466824434672262229322217169307821341900542588245645643195604631233191463494829273351350637502677221492499850503323159599856820125910001399730670436136386823844322255595566389113926344809777643143471873799818746252295473430495909344023151509 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 58876150289389466824434672262229322217169307821341900542588245645643195604631233191463494829273351350637502677221492499850503323159599856820125910001399730670436136386823844322255595566389113926344809777643143471873799611968573187145401795715324809839509) (b := 58876150289389466824434672262229322217169307821341900542588245645643195604631233191463494829273351350637502677221492499850503323159599856820125910001399730670436136386823844322255595566389113926344809741451892228564609484929388837379614717852874543727509) (x := 4687907158474477052608198042399470945259107601693786171579967086647861335584890013170757628731145432489688786598755946163425418541172194664794023961901021940902101931598682166604117652479473892221373995415423542129247099233997426244864589146636252426556) (y := 50946995749493218697062609543347017851500748187908957924839370145013869316234166316153388840380325991350862456861384088196374096978185794200885486707748698415934530123954447250614114114540919934661620301476803503951857937455559786844112176284078039480498) (discrInv := 20787263527911306061129805031770016174588499067021618135277970394136394660478206562360052919924271168575075779896964049101846225556778494315351213979897432863447087336570512325648793357391189671292951861005793526246759980571628506020197814338419292163738) (inverses := []) repair3Step37 (by decide +kernel)

private theorem repair3Step39 : Nat.Prime 11983726814746251627794567995330635110927112239162018290045404403903905519727428317875265236433194915978432059012581395265493755488867532395862554981547921051035890278698600432520063417014570136803020850506697154250443398920982695362106874885044067898401025590237 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 8841177173568366366817429394326219736628735193055022554712052182701084890634947874270633237979157829381249802618635433766623755406775224577911357561316462060015328403881219811947327719187210081255936648236739849339087953931161832065860786847951909666228800149639) (x := 3374324038418108705103123373836070195180644940488408458722987491409847527346814778559689725924975228509095182757722394727235062853925237263383143270671542784469955304096824291357874436676119884200056348972609113677960487913656895493078460809343234525937128965149) (y := 4396401067958598660855187621967905007482962854488794835600653903067727097276266895204615293320930925048147192310418442698417501342240935623381753191489761023899960042635913161819989471055136007591371781849412762061056024588737156945917868014602392721683155499574) (discrInv := 465213736428805152282549777725842806555226838221537008230315972135289458555676817688750610672730359809934597874402540690523128580888213008338334957188929817105677613686091399625629951503595240562404575074914316701120813457116627610563843231561685870026808641793) (inverses := []) repair3Step38 (by decide +kernel)

private theorem repair3Step40 : Nat.Prime 133866517604050873469390130253491689676272401905830309782419609130459900728512432185559365932614665322121759244842375747392493411192332556819063594496110041367174100478779023458528142873597707925753949004914776467734561105589509433412516967786437840394562128144730966842494768061 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 83604898838337511449667160286170013534330558875046449257639068131332732212160679902043044511500872741925259308334416805589412068834549900842610329633412568805392182531518765200344677503910399723797005694139686405058254154741432766347975608140763644310496064269766155311226185142) (x := 47446165473861792376395126903079865542493813912418543233495353895369112351522299000326596407473533895192761595084599718316308548577546358701599794551003357946781045824018233613052906953045737573818607954779063288258889211752224914642406692806844323542592895527734548638363396677) (y := 48626688420134307015225014564446320508129488390388309689279979007181169736610570350967480480832779617838941687983761719654821991121364023110057450558397506837755561948818718904388257752464217891212648049885217761089147279127361192217462823389941037194415922901698950416365689785) (discrInv := 17764580528426644859841655393247429667968554550748753584769767824798739307144168366135451222932458867801804730538677137848879730508722843730553035766507299993875313133692783197101037404304114149608714533247366730449409159489846526531714194178728974586654784593264840508418038325) (inverses := []) repair3Step39 (by decide +kernel)

private theorem repair3Step41 : Nat.Prime 1934638912413743223379626162423461899201488752343059636975528191153406485328461669945703956458147143235303664606462014301316314778551590111151879766940340040696173899176895886558887431065224985189979505394667730965609419630697319975415220480049896276571860118645132374924493189869377 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 929598678061922395388749476730781252369825512013035560544933548095997120661805313928685044038539082665140340021116117207634348445760430529181504554776577548845032264714691227229820044864937993643288240499719114076654114450903813126305716049788847776151818846248706908076511875154303) (b := 219959325370898707371409096551060578130267927231056651579512560027298745481676098553278825397372195219313138304572181445232101660267088806865590312586503373811941218303118626313914770031506269626869666722468386931097211966729109340644320261399709327627986339802293720622694475988428) (x := 1504857537762375822448283643863422505824930298800369419077903376669392768635352510337560003991717060734071900304557530963118005913210938319707373083346503922021638079177500738463299609665601122662441332696291678138821403464784362335402830259488656328061466769070632613754592660328742) (y := 285764196301012737446696920282342135447612599856039414214794333445537295760199072160908512793821864150182758373817292752977586389496792713897831540201177131001136340604385987457836499421660814442153690384907290973284647825128963604945147393128328247043666192899691042941446166825957) (discrInv := 1628645211329333301469944563695497285709663342790010877698352685617648465454885854999383969606663234600805287779638026696663765811679170593939889454517246127035079886563605293493532587288819152899726676359238452327360201804231403528096176803620846809136659966829721123486398278625153) (inverses := []) repair3Step40 (by decide +kernel)

private theorem repair3Step42 : Nat.Prime 2879609419904411273352957802206877016942657530447522430536950985065905576274178115707343162582216199054301268976159172262765666099505557197763794710232051462791529886067819253878067984241063944665543439843852197142160327006570787379857304779698290815895126282443252594805267328876126298833 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2167894566743312614839582000160157854909266134842518047312282019254358677166429718882624653581272841464143572944170293818647253267722248351529990833024137952730124652515048862966144624152568792717106658136029425209269748368156095566783836545132601194802956070142443588242590440585176790328) (b := 2037981133247581712876730249875047508594288626606073764085465567505975013804168507073087709721372931954175996776511662229502931290604242640733281148066819865915565716438065572097740069352016359291230298317997432357681504048726981191666864206022594413860510167318383708444538808032131821870) (x := 1566097306384209443385192096707774272364920533396841755779629688625898298192241090767715751531520559043069153625086557744069269442218849711253676073401556642947141070529884055683902413012510565825509069115957066160771202190155162565311185824061910205728604947444158750903846393322588536902) (y := 1427960778194326585051252593350549994047889843624307486168540063467499532649358494150157438682160376225197505954646504247758513090828035978883450235569986963555429536098011074882916689585836571604075728942869164761421567793024401381534884667085310907382149777079108520615504507981632300205) (discrInv := 497928681453057581944271104459547947560367956087866931044396200399408421654173423577607307684012596792909172481492630216526328805877505254685187981915813183575011093826688921576514718309636997148323534098463093831754301406688300604184853214850783789913231838843644673785705393394964464272) (inverses := []) repair3Step41 (by decide +kernel)

private theorem repair3Step43 : Nat.Prime 613059573155317067892544519565721010763097232875029484439090535738359384972816917980560781668770314042499785314938184542208124207139892719509735094438292663932984121104677234196814667579628051722606582094413506583085813609016765541310897572480237142655957112503054986112965283831043698661574437713 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 302335573831838228446261260316870584678415387115046052384915102925790770450931101378367564314976850035007125177146209045976711720001809902030582863022227400156748634789183697143132472588375065740314467985862196100832212218713958637481454733305271663578770976714092999429186449744156801907644545383) (b := 272592077115425073026440204284026709013730712907687908506765209286078269714412705960180764511111332461350937750156803805829257217837280759315529633801784847184626220432163762365126192189133351704598514642709668464644861173826526730984048908300371587307249170228832328826097777476116571974179736380) (x := 400971923537825544700332868546966912545499064667228223113634143628798100359558003006844931981623712604367133241319119637138315072075882926833688692939069338583642555184757817614002678529188145044295612748650292127500134156768615083384928899972040106678267466864105699079789645779978329651240877504) (y := 575532800409872315374128141879858557784254446795564428953452498991330805497822893510021818982567289598218956916694866318807238411347507849756077898995744774455564608179825499470370456149472333140507503292833237712573747135629800293936182657013770407092519565701235132982306149696826965720934219189) (discrInv := 281948154390659251964901274596721174074535823822238267797822992836247242722703715068624347479632199262067395849528132117155311995713982750945668240533551878094130705744953228524022375353691887336972641523926643376944878775407656089459362325245398628620978278119614210971371288775205456225523256430) (inverses := []) repair3Step42 (by decide +kernel)

private theorem repair3Step44 : Nat.Prime 19643041783469514172345018951405266905860398438548819710912899855592773053914026869015148005449069632235735621275934370916890507720969302625811422160898062393198471155277222619909327285923460991248942439109326545373253357233821387930663277087857586057726986497143096941057187952131272509450349435808827 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 2138431826376807349928573917230085194020772413863582410895011692430559608372010605639895677353842775661526548195300737212159683440840321640532476715667518478972019678772279172784759159024963473905120957678736294634084641363792474365290292213644493383519528748778147209008797232073953375671076823452575) (x := 11574140575261564496846881159066359890695386456458480098103192004271812880028895605115714184297076791393726941867761186154605464462752238693776877016489757001581239605454495874048336293213095421560781954098501442201474736193378403320921925631804849751080565055610082085386565373656629461311264342377619) (y := 5920386927156319061450192911920694735314769495382230173805365275110088433677950384931696328102229931956005060418869393465504915921318355188546840093754747311268319356932828299002834925956180901108408402624425480226583679442809346894617079417396372892337986906278011471414444070511879265659248142947700) (discrInv := 9933565924620057002186885674900252830213576157070490643106668025016369228995853396976301442443169194301459709893886651948493591414579854532873340367120901775817671237250873123952683110550082422324440012094840213545798303956609751929957340480484002671980732054106285720149002089815072641599955305591648) (inverses := []) repair3Step43 (by decide +kernel)

private theorem repair3Step45 : Nat.Prime 4952450114243272364931888217507499949412039403343458813872166530936549760209414645314941252377634285098700093625115297642148700588709401024062730434117849756974618234456726931257993788385250550710346111980783653899714429699837974660719927115751643864655301410458064526531425734330855576095337423162091124307521637897 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 2849228354252279495506987910275638380355622624832859738505288049020139309786437574669678582774062794751268919446003677934913476544391658230447546568490946258074611560356042444729081673935750590170774610104048778350698204628130447503351732919300364946368663507972681025451465476065592309630202348323772189263449861490) (x := 3045182261711962680386567477202895158457246322541117615086693926378848522113972506957981759684243399146894440559269338679824632044508929528478599403449237577831316422065322105859875335830086248706255795070316942838091578400807356358123604237212880703964768104917525728039252894833949904247596711867242168179125928161) (y := 1108604282375784884271857264453999561296324611064634460368824689779823976055243498840591911792173649745472839843519715211931334250735358132738725163313345039522817431928372828359699005983881353710560371075781799280481342530483047320504605130762633883371330078255578592414259482261727051517559335911536829249190078669) (discrInv := 606829161013288662026017489808346904301606190044901494181938070279837984960804742086960917708899026849851146553923508425314036878165885238063793148993936209805885060567020035186038080301533643922954989066647232519892775253610650816089928115971460759044182365488304043028745530820287192223772132846749619724328346964) (inverses := []) repair3Step44 (by decide +kernel)

def repair4Nodes : List (ℕ × ℕ × List ℕ) := [
  (3, 2, [2]),
  (5, 2, [2, 2]),
  (7, 3, [2, 3]),
  (11, 2, [2, 5]),
  (19, 2, [2, 3, 3]),
  (41, 6, [2, 2, 2, 5]),
  (761, 6, [2, 2, 2, 5, 19]),
  (2521, 17, [2, 2, 2, 3, 3, 5, 7]),
  (14851, 2, [2, 3, 3, 3, 5, 5, 11]),
  (298990816807, 5, [2, 3, 11, 11, 11, 2521, 14851]),
  (220655222803567, 5, [2, 3, 3, 41, 298990816807]),
  (1007511747321086923, 2, [2, 3, 761, 220655222803567])
]

private theorem repair4Base : Nat.Prime 1007511747321086923 := by
  apply sharedLucas repair4Nodes (by decide +kernel) (1007511747321086923, 2, [2, 3, 761, 220655222803567])
  decide

private theorem repair4Step0 : Nat.Prime 3859544768775383604192457 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 3474675873221679104068373) (x := 546269781757805929782074) (y := 927052882810274905353278) (discrInv := 3567765720158068893142493) (inverses := []) repair4Base (by decide +kernel)

private theorem repair4Step1 : Nat.Prime 327119576422326271844785121407 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 61370634208220977070825674717) (y := 222177417814111073396323449918) (discrInv := 24231079734987131247761860845) (inverses := []) repair4Step0 (by decide +kernel)

private theorem repair4Step2 : Nat.Prime 883549975916703203589101875918063 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 711128663651161043123927020640333) (x := 173639292288631038377666049388856) (y := 531888681294089620522357440943065) (discrInv := 27787243178184168098054729451890) (inverses := []) repair4Step1 (by decide +kernel)

private theorem repair4Step3 : Nat.Prime 977262569634139251832147376839926785195647 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 977262569634139251832147376839926785195646) (x := 39800179120800738418854497152980087226126) (y := 894585186275035744990394756987987556421683) (discrInv := 615313469769643232635055755788102049938000) (inverses := []) repair4Step2 (by decide +kernel)

private theorem repair4Step4 : Nat.Prime 220317640468247450550578515252979527003601208600991843 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 25374677744655789684995711866607578753969361671876784) (y := 161067915404750313690347196185870601265426085667969230) (discrInv := 114238776539091270655855526427470865853719145200514289) (inverses := []) repair4Step3 (by decide +kernel)

private theorem repair4Step5 : Nat.Prime 2439644694500416940265777621572292690329613324448173315056837249659 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 1701622521750867373213743441935275693197379166953146999905594993395) (y := 975535103662820331825125814473238839654437943003209683578982395277) (discrInv := 2349287483592994090626304376328874442539627645764907636721398833005) (inverses := []) repair4Step4 (by decide +kernel)

private theorem repair4Step6 : Nat.Prime 18362185561023552573051111991698625759160920969722019017408356051163552785089 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 529319062058002685156667222187287786287533251212690977471878011512318573486) (y := 4462021723866620729993868718160968204449677532848566237656109896397047047162) (discrInv := 17682104614318976551826996732746824805117923896769351646393231752972310089345) (inverses := []) repair4Step5 (by decide +kernel)

private theorem repair4Step7 : Nat.Prime 64790087355766244115624720228950632818588234839878576467135227915523028949521334662063 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 37086685111481515752121163931536395790178684637298896055614443857248382028283612925783) (y := 53330473074444280557218751169879040783286453369975773130271553794022309830346166766011) (discrInv := 26395961515312173528587848982165072629795206786617197819943981743361234016471654862322) (inverses := []) repair4Step6 (by decide +kernel)

private theorem repair4Step8 : Nat.Prime 71333886178698634771302816972074646733265647090782928963252614615284250890353417047725821 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 52028739099453058795915507610511863494849810404674800477771084478372062069670568858795115) (x := 49938575135651608203649389304390176992289452068636661313987590456892540133149769221218085) (y := 47591058562480263877748340357729789936621424116612271087186505407902580292226188607775393) (discrInv := 57739167784340176065423126425643824365947556237962792611347782533822884365429135504037599) (inverses := []) repair4Step7 (by decide +kernel)

private theorem repair4Step9 : Nat.Prime 359971476484705133660077692258010569063611102258105699559677220654643784830028248469864937124517 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 53613427065305471914113388176939254509989406982318973066339244817900132972162255796072813674849) (b := 0) (x := 239172981716093193881675260402342923477154697686183042896616538365380249201382251872803426456530) (y := 266162020906480066763589239472712116293941662977978815039288972922731994456472428797993509588916) (discrInv := 283381964129855218223586616237742740425205678439159017936342726695457871865561750301416906262100) (inverses := []) repair4Step8 (by decide +kernel)

private theorem repair4Step10 : Nat.Prime 5999284627094095757578854819172004144014142630233744285768073354423553962359211755129010031807009821 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 628089840815969195753457652611778397585790966658477898937083396207336814401607590064238286863290150) (b := 0) (x := 493541161913627276906371965948217856871248202902107136718079614853686378018049081343599501350600725) (y := 4382058563313853282713408016414637493697110415673547234759271183042905973228951463673114647542671249) (discrInv := 3156664773751040177727791822738946671403519056781491617618307526263611184780007775080564587619327448) (inverses := []) repair4Step9 (by decide +kernel)

private theorem repair4Step11 : Nat.Prime 2808052516591912076792164100856450904210302337159674893480550307173606976348865442960838820362258598510023462582175537 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2539168766413957370603131512660437307456065105994546776813854136421311242470053402962261400938889631892666271725759645) (b := 0) (x := 1116108894343297888383427143074929377591766174977410312319592941690650699460233288010538871629591100555803843923313894) (y := 599664769007643397149468967872198636437747344129115528391836519000188484233750616270465940612087441311528479260322142) (discrInv := 1462197492036413858326395018915431626027118464938633509192791501714336778710561499731670178761119815214283824330421291) (inverses := []) repair4Step10 (by decide +kernel)

private theorem repair4Step12 : Nat.Prime 4942172429201765255154208817507353591410132113401027812525771918072499583344347333460041284847050497901734696269400827349 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 4899024473174886714573289339049725383189250910875871345424909222589851654891638013634982469020429518661354867688865352138) (b := 4773466176572496889172744494861273207898849800075075636339167717376285299130685699815682954135891268027860006563565695834) (x := 63587786098689421313659015165846792569282661778289624608093850877434386194585127524465700461478247193772695173870334514) (y := 1780019512458233285302962283125107207864753680392009105898544450425655965762675407262537093503768557961236043745828969831) (discrInv := 921575266544633377349923887210028971108835095505683943526425536630386354895286771704139134352224716741250684019485306313) (inverses := []) repair4Step11 (by decide +kernel)

private theorem repair4Step13 : Nat.Prime 114263026563144812699165307860770015033402254461831763025595847197299497858665593988892028629925631707395430053414136011471337 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1) (b := 0) (x := 106245025663333208725333823540121647315019540641361325449094049122575946950129554786154625962198236822530140969211189016034771) (y := 63718831774573045143088806896939509766708976020534886717508481174740096180420319929534750412308249949022490764459147433200893) (discrInv := 85697269922358609524373980895577511275051690846373822269196885397974623393999195491669021472444223780546572540060602008603503) (inverses := []) repair4Step12 (by decide +kernel)

private theorem repair4Step14 : Nat.Prime 2095896759334805755399862060779444864013758802202711029256591919029569912584814630499116319224823006709010694493322965855178358074737 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 932068775496362824353221089232248236229802295785177466693104010924536550064011099598436436652011462455852937368757214759558469943392) (b := 0) (x := 825616992257684873626965000662689264316226159261741417482428278020908201110512514629814346105734937750725589161033731844350414054862) (y := 253571125217462589006102506949115062226796458624443642972458327496981523313699841929585179041534286398265077449851198755327335366244) (discrInv := 1688620778469814593214878171010066276082808316487091144651816586222818137883850265901097117256641964333544046651531788888450740095533) (inverses := []) repair4Step13 (by decide +kernel)

private theorem repair4Step15 : Nat.Prime 6287690278004417266199586182338334592041276406608133087769775757083819024752452771936673419871916637614630887591767978371575900891849 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 2115107086975234233391943595900093794619141130328759881967048908100742659381678059226169517935238560487796975472022022906240066586128) (x := 3129407565024086831204473035299958397857675381856300990533699777797387921367315564468788538607381952109755274963956050211664642720364) (y := 719960611481000690794702159310879468688077380341316397947663456671621476559622312417424664537656666339554041207355621262044217372230) (discrInv := 2032339965360371749512697546950563965402539619867700629573521230604507684767128062683461282525722306856324824847828696765923937580195) (inverses := []) repair4Step14 (by decide +kernel)

private theorem repair4Step16 : Nat.Prime 100603044448070676259193378917413353472660422505730129404316412113321998708135316099895624167608629420008389537555612956839244916817849 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 56861124353987261189299399296928401987790395129270027054077140675946980071599099099258572238692275598936213719575447881753841969495785) (b := 28369794445813783797803316960285482563178053579146057487743312128847545647748992683326251334296317725678236680967086460089929514300977) (x := 24195015166100505164627215083498137363968953944451185960648993972349538366742693850424040856750522303411819446029156332276809540494902) (y := 80708822410548036193959498270355173357372183616228862496120763297520849098700133535586402057975721248240625721774747749137743820406522) (discrInv := 85744483546819039853354823312228132202531857002008295255755337223368261845994240274291461514646493352615115349138546588115014858851187) (inverses := []) repair4Step15 (by decide +kernel)

private theorem repair4Step17 : Nat.Prime 9408580216736642924673261565079642178719936845346532153647704333973567828977042243474399832993136535504889814823553497037760796661328668897617 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 5231463384702594517572033662240261884852445573609942165815674855595478047310923945234545551442213519020833722927972608738610601293007762367759) (b := 168434764562315996444025334950114641666556642213158193197318363030659475590346021483125078032409304204507437860812079208270834021101804000882) (x := 7174342314432114853006135048367739713949381525874015905881632075345637015957699866531276653522782455230554919769822189889311226515644232280501) (y := 970589882711151502292918729596949195935705896737048688916279289701450396901748842069110704352182611302465733562955555044705689116216313665914) (discrInv := 72173253981582911227765711004842450012656969822400841635905063750124959798552303200196276315378631748365263941873223553333159038262636905599) (inverses := []) repair4Step16 (by decide +kernel)

private theorem repair4Step18 : Nat.Prime 376315067606037457687942764877844533939040922482756854668236613075279798216789289199613842132084942783060356265864499718555677951994008074315073717337 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 131924986410790804477811371339296873890458012708948361505399000717312105232039454527362469930199041296199426664733940359131433261300362781391334773873) (x := 242965601044677650036884854090223545948630570846708393359056523080265279923306815435386775537365444977368712761908929715420281962410968245910486263948) (y := 271785445064315335336747359740227457751941627663338327987243525323566707839296599482635923202857475041957774049378285815669904258464052908426079917926) (discrInv := 217919657320846825173891627825432055792966809515783897429013597479666966675491569395373972589244345005185725483342900430484868653823829962188443177231) (inverses := []) repair4Step17 (by decide +kernel)

private theorem repair4Step19 : Nat.Prime 2890309652876590068073710171317823556765413302935750319076988710574419024845786261043882908880353981180754831123267383990646698291062527960203232266390068159864766658065864538697 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 912264986974304311804332566500995208049963871809371612089073582459497575471713131604519185596203120589477215013220689916417939083709033084331819600782435549392194907249497337083) (b := 0) (x := 1060554488325034389587273697229495744982426246690337572624693320793773017291310212677966524207265849717514998094985755964528616695010838426835519849983168113658259182854244234239) (y := 1645369515120704461032596318109589728468819098666743332775353595828143086580912010545287945981215570560271600932143957530687484076711940948718257729044877638006322579776111189945) (discrInv := 1939665992913866473104199486863118865561569009249469836285473137315939874766411412881782385261214705738196819589145365513880538947369637699069469299596942232550526266737024069752) (inverses := []) repair4Step18 (by decide +kernel)

private theorem repair4Step20 : Nat.Prime 1183388866674598419770946405161233207941185450159493033738894495346821128098497473734945783848644834052181370603141101927941697204044479776063329395767363634442499445341582451931989961340073584441 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 926615153679333056741693886919356356160450450989142373633580145908821006691301814630405371645474043158157365368599303272790350696222556312298652153934149235983973262666337963445869570587707021653) (b := 957660078061065651908946429777615500281993378230501498649035178645951876474434473343336543344963682653638086867848426629911126954899385857384576943169678768761652489306464016676859756595388687041) (x := 22132215466667893027034634005159982165434534935054967141193856705975491738855189894677587262258881724251429016468285425552312865782315471262245349101774548101295088476704059430231771480016334391) (y := 1012005811820912209872932177174005625652541582483962393849963126628691949289098958413118163957497898258752826503951302370476579740561768878811464559832070878239189961499005934389276427770609554160) (discrInv := 417607275383683026779828749237018083067077499362091524370691668247380176232287613597523026556124232130276274307875941294238716183260868443929874848860940925055019256486860350446643979568622372047) (inverses := []) repair4Step19 (by decide +kernel)

private theorem repair4Step21 : Nat.Prime 4733555466698393679083785620644932831764741800637972134955577981387284512393989894939783135394579268038201172944535774915690944172047114406093218392392168949874148054256483696374540048070670699483 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1521466382043508635252882099331158752664954803075189227692663712533035645908023128457163930956813749202023124212788493899163016455036173162191835466889499068022425884126747707367170821188388441147) (b := 2188144138269042194299473299811128484781896944209028826185819106544452401658834137785254085237251154515822276011374029660552865029294161018066004505742394168320121562743848322054025449701663873961) (x := 1294259414435032189017856055637805964480791265887983486348735658888004153656770016160343083869594047041400985163604112783502519199759922537858347645143567717684967429156321414027564904947492300489) (y := 1897062811711718592660804958750870802606469864437494749758778392649536582429675509390305684114140631545328785083557464598294009535919434722227275127561997228093130933766734900680776262493315963700) (discrInv := 2891471608760692531453994383061064381960520554260411583648940191166199775991394673916466602367976062535509553262563147776756712930197832304208210612371653060094535409460699869969587142471648224915) (inverses := []) repair4Step20 (by decide +kernel)

private theorem repair4Step22 : Nat.Prime 63823224190148046638957506839641864175810283115046472077509896393008021011431487669987652162646015274210890982555511909603285115039550045313375169776070048568223032627272666944591659192061934642414809493 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 63823224190148046638957506839641864175810283115046472077509896393008021011431487669987652162646015274210890982555511909603285115039550045313375169776070048568223032627272666944591659189713656686855385493) (b := 63823224190148046638957506839641864175810283115046472077509896393008021011431487669987652162646015274210890982555511909603285115039550045313375169776070048568223032627272666943206585789985848136582361493) (x := 63439814207191820499344091927468194376826647250651409439925221909966753290738315267892953197386704778868796108225203352416064517739721457018629839734160654785513147401937180129581203569141118409655389339) (y := 2944920952130339837538109078276275153562342289061027461417635971199974431888668944636370175069395836416547532025347558676398377868259084778674452312716968044899956176724477016361343400892013136102555814) (discrInv := 20806642642161222603422566786173157189271813837355858999911856370178624257112188946683154902793300458952938455999600620681507131107343574397668632457012557489878833915582235256197625014342372624709786645) (inverses := []) repair4Step21 (by decide +kernel)

private theorem repair4Step23 : Nat.Prime 101094710652710702915175911683855920017199972248571310841334125688596845121687247839507041272588035274044091819432510520133244373883382297116941085864033835402274600312107690973595318332281044520809351478764761 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 26969500549262675580070001350057889358055383352964327006001505433436637023730981229869872975271210041045940793928627002929344689926120304719154964850925842061055120622464256448075572003578013033937325402225259) (b := 73924761050773061410892470791040385398233775758233423520659429423658030793069676332431913484426932070536995203595156663411132034077800064929247057494088921979846010125183995390748958173671619482020880169030775) (x := 15913232856453727525539094797302668766806652705682306269685094420009463354126583466315376359163401804628657961593392910093456012000436764868973995569409222423122541599242907720175350389220898992226988344992912) (y := 70110874572976892488893950787102896738882203901782085102306127048357159517031017167889860537383759668400461107045747569584212441761249118434871533289461032955095990547744693767973846894496673327355569896453243) (discrInv := 13879926439125015980997903229310978231834407342014088374641955403150896641400463771198260088934452760384650811366558023650636582878362180466346080296303127988392846901289844244656177854386946457431371036928573) (inverses := []) repair4Step22 (by decide +kernel)

private theorem repair4Step24 : Nat.Prime 707662974568974920406231381786991440120399805739999175889338879820177915851810734876549288908116246918307050968574575083267759978768470046491850703183146885625310091847853814120788519932346579807191403200551213 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 199223524585909079980596326663254715509011608676517338141447132316299050744889466907585709854628647328947108966420181747183371763372589659071842817044385879982982070989540377187990099650266507533283544832414161) (x := 32844337898859110352510845222699393006852616912101052742774041869703449977079710666514090896426887836248743798324592777359625926593411034844925618842473767488138711818755040587980133771573041585929768815952502) (y := 18884574290670232162274878396448766332022268765660913744870624504944604429652691204789373114734818043719974062843890102771873809925806612084111389348261972288425547672092467643064033806336431936257934821781522) (discrInv := 42584836488498792155209167699017934134531127930062551307263206531627391453636113381809157930288951617542156885981178263169714555273089224865156505636873519362951841212057394628186181762346788681183652160931306) (inverses := []) repair4Step23 (by decide +kernel)

private theorem repair4Step25 : Nat.Prime 3018268921419575450472866403550096505069199860257396765067488821776396872813706705158137656206362583288703609272304671361839763879440545414182327895644882776446726319502854902710883296275428348266614590270327946344949 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 601016427529144206028652641380643514385570026584917220008033167978659294451156257284045845437558614685546616911347264885376574310721832685473510210531909536673949599928620485493584759204092829653873628510249291235623) (b := 0) (x := 845382594164907503429909129173191691911612200968421664977747726562222730211122095554404711011091020243305685110093784734717779811231158447385693283074139047790061318814845537605415129038869575315240099634276014352669) (y := 1270758090107392523424239162498105895255077735901920063088395031384676362326305881408188817736978720638693099792844877716967722787057516828987567935208853777755381812631487636336625112961957799920645627344743415535925) (discrInv := 904821337237179914125379761232685004863692471710578496268880497438764041816215740610545875410980299493562556545912984061804084547540594524913959526544198078280168979857868847051117013869880294480122054695144309395143) (inverses := []) repair4Step24 (by decide +kernel)

private theorem repair4Step26 : Nat.Prime 12190631223629751426536482814885855178956234637186892149475803841736134596657175069385049770259375743048742865259677871215478283292790547973436111311809476154433126704861515471300853921648307719707857926302512613202989021483 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 9108265877106436388082882234151354287125064203340710457860675399544175704987493767874217124086724772771259574185768762572111389562566278293779618434232818338761990081642039107400675206730143644381893573949054458460504413070) (b := 10499631438095113285785194066265726433214099790178931538765310492854812477020085940963549935354492042964887909541153093673441728584267937573551761653688448394305560609207066523359446214254826326601743323181191439034797285704) (x := 7312159858241375409748208483994245604378152243409095136998939438752889947601098521631896727759211970522281159083564769639413141336168370230403584699555220525452919667316296942223803592961534099140158206250332210401135221447) (y := 4320212714732749485466083115820448873093343861133426392965811149772105241865115994734685776570531929049214289960951158715748172990818194758493846079627553202138039561053905667626441231700215850342223499131126331130776853808) (discrInv := 1807350733463350798452794524397685685236242190277452900441417208800568241509911908498198546043157450457225300814402312105405490951609249903701370816301167261415225742807644039497464679663209474063811857437682824879374624465) (inverses := []) repair4Step25 (by decide +kernel)

private theorem repair4Step27 : Nat.Prime 4449580396624859270685816227433337140319025642573215634558668402233689127779868900325543166144672146212791145819809970583785860195546430186551068488545326894442175605632260127945007865927791679245245398718811267760946315685809 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2263675853840840619695632211288694414157733695442271323418163865957306471656407761332173830298460262839651195651716137703178907516136788884124690905607395958131697262768426929477243448573204460166291915412699822189421317752978) (b := 440239850246081486631819582723845713556657422768330682752983419704767577791517302459824809109398272688779835014138327729255412032117276562451225754672835103359901298550409117623484299003294966938971919892357277990673118869338) (x := 183286136539383447086408629731986748438664619877106958861409424509711838008857504494353237753011788047826719328454859333124589050806256517152598365280941884001364215731790800327935296430949775985423310928321702146224127705032) (y := 398346909546563972647058516606926444216895152635455095234219600288199289652944226762867585785398694125533791720525616036467366486724853241321851095932351101495835554941394227795111769187119632921871002769423959495526460711085) (discrInv := 3473661182227969221644368128194592515552056476971221552471461815400975840774372935683365137071683240708397813898725277077182790417091607621748049861448389966939276350256899832661282113100174779865060797190228432458804045216440) (inverses := []) repair4Step26 (by decide +kernel)

private theorem repair4Step28 : Nat.Prime 11696540795321421567103474143994374407362377602221930767114218690257262871168896900383350112153841355995224680358201380785157802488140307460109598656532797934165946712132720280192904595248289670942521638815053787196304422617605437117 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 11696540795321421567103474143994374407362377602221930767114218690257262871168896900383350112153841355995224680358201380785157802488140307460109598656532797934165946712132720280192904595248289670942521638815053787196304422614214342333) (b := 11696540795321421567103474143994374407362377602221930767114218690257262871168896900383350112153841355995224680358201380785157802488140307460109598656532797934165946712132720280192904595248289670942521638815053787196304344631468324541) (x := 7196498148159145804979341537272847247802442712128777552196362949575225240016216072840371815200727786345257420105457734777307055753941147793742971034282840722970622523180988263850644541744417365881296757423490749239176349527741299206) (y := 6387678847063432825382830921347027455422052884945147272641920075660727951542712316825902600960159908607833069222919911454815908778142578414483917336908005691884456832009954510236688544390427499978524665469428258860199444410476709267) (discrInv := 1133671667637512596915777992037924490942565848261425775455848552908789706113277405382104254490531117717187164361307404699781550890007714279187198120706864945244559367727278916258302361178918267919249563633675624625286637813849382466) (inverses := []) repair4Step27 (by decide +kernel)

private theorem repair4Step29 : Nat.Prime 598871265642615903893967176875452208699971793280253035396400234939227196972428698009560817493026800662288571142313287075775452521259412644264955519195364595503863635521914656216350080470876626821796482405048910659440073425179518051211847686253 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 9380507042834038991560458197349650917950197631095885463251582509659243328245174043376064508212269604027056393065858186326089166751228857909044791874933959290613752534266315303600986300781641401536002440796456133281434628881780671498151200759) (y := 278890483301289559987195534568951490837259714988124593066301767846303796173452702378311010816412884649030239015802891478861338150922150815798455065783710175973857671908252503875366719880041518426210246768922048593069279892567154365566189363474) (discrInv := 310525841444319357574649647268752997103689077997168240575911232931451139170888954523475979440828711454519999851569852557809493899912288037767013972916114975446447811011363155075144486170084176870561139024840175897487445479722713063591328429909) (inverses := []) repair4Step28 (by decide +kernel)

private theorem repair4Step30 : Nat.Prime 123383051375285584215658481582941916749620388682357411870578754803589222483441594936117776984818339633248665158166237283073705180562854005146428746059422753974237780842605774456709872436249389488644997184027021882512107272564858254046301236202117141 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 19513260576975289286053047679436727826623183715386995628091778983356090596524038484903479605659204375195458513459542082015318008333206073457242079622904138931641972259068487620984007948403184112299699149629858290514848156859674713132904420223575494) (b := 26669290951392337366878462522564581408827457930006226140418525637447105559424631159288694892576904152898378002334025665884455607917373655017502907862449846674213837588121005227091545747204276726669577388721847262568032804267467317706625641584786246) (x := 100361352094301257165101636199876764060852164705586871234816882037007752778195748805241064470644048341148801711895489804765846900295962091737042350547201161515061285928885291378880351508162959313198978342992817633122835477083157468093782834634835469) (y := 21912863940053386082878077605272755440648418122917123761456311033224015265062695627239368257932707735188064359608308941597534734752929355242911797621481645602203477479495960580937143477980255146939418232697848049598584515963917122510564388713967374) (discrInv := 93993454975377985059659224664397913762867772492394058122658015403462642337678885775708397459331479771081378637909700545934432702710781388185307784018733283826942484762959248127279954767318602051205396446257142691347322216806322745964281092695815675) (inverses := []) repair4Step29 (by decide +kernel)

private theorem repair4Step31 : Nat.Prime 15399779919669497805882275597727039046861850161440123976168168407871757585947734663428453047246316977153191464198555563112754125663999392625502984513813132178867000884848723996167740775351238547834117250699322392903035127159849712708405305285265030689059989 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 13389903233265875348282596397446549857388341038653837835491320128286586663115082288989245097503567760205892182756480404200934914113320395540821607731409397776982898649581334300406328087148536603519023210255317219706419823086231887951378249348305813270053689) (b := 4137871282033486078582025043719055498648291868422862343923814264021887597488196067741631710159946852335574252918280574754528947810240437786463248209762701029627881791237747379612424047919900077923109065237939544113849991377532882778933160168482244268912949) (x := 6894550288994968753479140750966572153677795919066192185071933477496599944220007863949196265407167280380415741785335603198586545957070279086949616532383802699469626612369716395806038803135771444534797559086211364473999803104703901363782412245919345674169043) (y := 13476069343856394934604876045097788098679085788193961252863237717709946514467520843156607111893160056847097961257718157399811790421526782188847063358676738871619360946256630201373463636331719320403990449106181783937290021342990746202131188614597287518560739) (discrInv := 8651100806972758383083924810863001821436462286101420121013109635760140245706737340728213781791499087532633064106290101051193625029769812508639342838914807516774073964052418946444340560696125378748488777285202802222175769980249380343429386547740662515403755) (inverses := []) repair4Step30 (by decide +kernel)

private theorem repair4Step32 : Nat.Prime 64186282705182466854917324691326298747320191472882436732668925924009485618230158077169792300922649160774502022779579587053959195782272279642377028969205179300062743921796491960589817106114023196152734293063968241497439343474587007810960271530975537090183774181 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 64186282705182466854917324691326298747320191472882436732668925924009485618230158077169792300922649160774502022779579587053959195782272279642377028969205179300062743921796491960589817106114023196152734293063968241497439343474587007810960271530975537090183774180) (b := 0) (x := 48482775992378131695623662407907077412761671709844110505875732919280284982659533718384263573293219662544061298737760216524708702674615276651758504697553153245053107204562980198529224588767591550508393866006964406277370132438473555905376455587078145900928882499) (y := 48481896991708370613821231967520865047637104131872465323066101934835476833300939744142855410571844393432142719419470678048054919997152038505926664767138199305941000415185532419791543238542680217232919868871345876417858240941106139208140628621141923548456153966) (discrInv := 16046570676295616713729331172831574686830047868220609183167231481002371404557539519292448075230662290193625505694894896763489798945568069910594257242301294825015685980449122990147454276528505799038183573265992060374359835868646751952740067882743884272545943545) (inverses := []) repair4Step31 (by decide +kernel)

private theorem repair4Step33 : Nat.Prime 14506099891371237509211315380239743516894363272871430701583177258826143749720015725440373060008518710335037457148184986674194778246903107319289109104297606582072836374578787231083052054554792055464506909040189189452510573687170243777383242942170614665249909440917 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 13056456594041904042132316867804115129404971340254352752789705820802194832678050696186037053526845721823815311888530340224147809791574509407638930508599540656162163057503734315989836805846097075838917734319484655049306043709641054681646931345628553267045133838194) (b := 0) (x := 2746151728524884808419046966651832140125458613620504805321646471049838332214499217184590445664995972290621377674366172555707257274321520666233757834896157119801992814886512485502401887228818633187963137616382265334749596425454864921500850087722446802704961860565) (y := 2984279732272538815667285087471459613745104615050505028446768120255511110287172927837505325311565898458709037223618255308301120059765225233828751731536478666228686270113677548130212532004961405032389474650249677704519545636231234966723951044672353033091005157091) (discrInv := 10517164094196094765138736907070900540798424471499303538989015084613620583029520536766695793385970785623472556546225078393134341571345181011554287179298688455076958951665327194538985228738920296691982888099965758488581797770995385559103354307492445649386238180007) (inverses := []) repair4Step32 (by decide +kernel)

private theorem repair4Step34 : Nat.Prime 32218752547922031251075726209325867618319054720246106293785688513332783522259014412397951872131654312562997152829772839880884580619800808189900934276651155879348930827602394202458035650440102361798033118229250578525641025601511353206080904858667361984585818398736739405110739 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 13374303240202319718936892461674852199675689467933138458145817400365660398582550662037378530221260331098623269505470761896801778965214209271033160502645350893364886291913448568295013998708431779752863246477664872330988568523565969809133388111734695926485208948977604875074023) (b := 17374755875081534649571285678966049847430401011799512230572543798378405040628442005157830208061971853783047594782149771224309486678084520502317575545522776560547633136736387504189768197681770653049034502856476045732220478120505433533054821678240916276000837117121919155180885) (x := 10106401923437627308440370570944376981208584430986725411756076784005172728171485362757682074426308771760151028378818080934712433888378049005626565299208312148990285491759721786361441624570833422169934422180239060213065794543465149818223413253072025497998429300558326413258895) (y := 5770065934351974959136572440386003410283276828112427920153219012776062848896541420731493671360786353810634452046523351831886904916211031950630409274631698015739242511566820768702001675526011513326443800620547677993473905613365383938347076627133458254691299901892360170042490) (discrInv := 10650074048580863719736266150657712072796648628576068326597056997364676356676805780940591308250587006700969294165005237264564658460791634949307116496038988848356658286378501899756516918116893077096018776794779843891738775169870356841178014941040270040385707955043329214401625) (inverses := []) repair4Step33 (by decide +kernel)

private theorem repair4Step35 : Nat.Prime 116567446718381909066391977425340989043078339977850412570916621041238010783533114144055789873372325302852923698938118134689040412682439324009815214970568126727184270432008850358522989524005896988621016579362474383049127748861489673153776784526755106688865777864664845168418830699 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 116567446718381909066391977425340989043078339977850412570916621041238010783533114144055789873372325302852923698938118134689040412682439324009815214970568126727184270432008850358522989524005896988621016579362474383049127748861489673153776784526755106688865777864664845168268302699) (b := 629407744000) (x := 82863988478058660888160979193655515040328208871600099846819260705594414630853421199949762080341690037715174090605216555196826891625863747834320265977357436169769411176191793968189055182793257961697552949298888957335012226837769499015678281212740686718569264490030962738670188893) (y := 62264942450138366920126751063554061686413183701012770055255708039720389259758373375123669721556543526265104095367995446755814873133943836745607839981755232450319968372458660775234978824762426087215127243736672363769839440810143316266784116093209308549357892671433445221591469821) (discrInv := 36219543194670749766455517771487182189355764625460007250848761513076448260997469451810925115655664336202086119459654479873045649307285493679452357619079094671304505040243882103320156743642221505590405603651721164892377576270915312902368202562130036539562303874584754243341105023) (inverses := []) repair4Step34 (by decide +kernel)

private theorem repair4Step36 : Nat.Prime 308955489750055020593564218215130472363292727724253758896110532739023038253150641184427803935140439364994714500308341581377759027551695211685904322570933709028214680936604405064759131572169152027331455062901433521297233541390566283902858608754849924272056793860980255820919284316572001 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 85303711173408193327288378901926208985251959807574557558260009586310129753465596364249450226817195594342752214024032895355993720195905024305212443972102322136067269209079830120635573772875973458985213941453698698837457996766848166529785155555597356660389003243557827827599871341219545) (b := 133646631446762251818272311709681532324476209469348668320001274203673746186937450036914759344849588027343312179537012926866956859533760727767626687571418540018940636991777823279219275276586570536596672429828861718251245056242428634518827290195083029280717000992067502108915286549842496) (x := 265140179947797190575394844449186485664604065208153440267603908019257927179668572574402238750226132250582895077052928254814149730485339463224633425878608181541709515274832964958089821681564229494030235136586837221233670811553606421041070366096713959253514646805313382994334494398923540) (y := 93463692910332717048218111888888593872317232438074327573235182410606387296746514413882922940330083564514340593999928347733734634260031483180943214515242664094871527723061699767771517819449191530162726774590677570938522018334494570066316560609495727540922048874243631504025493030856805) (discrInv := 165710640316162824223824604129629546748722371136744324451874317626873370719724819685813292636150147937865663242937675939714112700712630163969827200207146215813123686398980396045688354155088278368527074200567556219159262379274885144371632968481142658206265131861575727749228133028756086) (inverses := []) repair4Step35 (by decide +kernel)

private theorem repair4Step37 : Nat.Prime 1235821959000220082374256872860521889453170910897015035584442130956092153012602564737711215740561757459978858001233366325511036110206780846743568853808219308470492415166567299909806186215271436305942189678653416405365519142451339237520089502536715807168895829512119497778504692798467873 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1235821959000220082374256872860521889453170910897015035584442130956092153012602564737711215740561757459978858001233366325511036110206780846743568853808219308470492415166567299909806186215271436305942189678653416405365519142451339237520089502536715807168895829512119497778504692746799998) (b := 1235821959000220082374256872860521889453170910897015035584442130956092153012602564737711215740561757459978858001233366325511036110206780846743568853808219308470492415166567299909806186215271436305942189678653416405365519142451339237520089502536715807168895829512119497778504517024357123) (x := 690862152350636462424948180820873286464208724633089567874983734113834873582460366768168975215279652780014797611349120380752971121691805146788023969814622484120593056530409261238529459758415606105773717263007265355873737845063414849538012040257453465237745947513351705145001759157398411) (y := 449999938692541454200823020415445059364306517736623993030008004092105591327069718518665301017463417672632344526747310324089022458349721889465717681102921988703080088483028200768729554797697252988330177343056642624270026776664515495216919519426339876985489932741448770660561080649424683) (discrInv := 79842336904202816250687208089780718175978073682104859669988435365919831675432810225470757649524337787223417500147367331317437160654498451152565223705761675704633820356232402780498348843305970128995126721522114148290517022001582019154663840274151928304547322483643236709915443768265180) (inverses := []) repair4Step36 (by decide +kernel)

private theorem repair4Step38 : Nat.Prime 299830046501016493913466340050447690548302747688215662359981876398569480440808620624891449857626483426562686309198012254792477435142143728788419394706702382433941064111567771935412603242011064797296991639836386250675973270938523329131097939260203790723013254057203920984914321562446403744590885729 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 229478721467403863666518606225704315498388388222883781675251347542346020034887858134883838482406572517063917872082566771544213090522632476959557805152820163871516188515806876838775261244408853234360638206277622699805195368508544847355117936641812203590530144178891666375072858216822947315618316132) (b := 10333880578682049230093298142288771370497143533807122062216415731600696035241262280530474433334336629838711747856984647325612555373507912701005034847914964701671642421307959137351432699813979301153653730284815619989210581517999390479246759425993580667585206371160448566006780294840480918402411246) (x := 148924932400804894244019556766392577684809918460938993964778930019842311407192185738566859902116476916915470276373132323436433442927448344385400322421899434172134327850548650243694306352029098464106198794580634593364469601406400052236174279440345002087123293126928401610882300036271146366779543971) (y := 130649660586988648465028673315495943036098298984997553997695873718676871940868281998903590500294057562582557986694097246953686247564585642337306993247692566693841679399611878813660477019132289876517219678709906964754978306829716968737628364283810378146774427059224854424321912401157778899729823702) (discrInv := 161327677562652343256759823307407171967470018265694195036406861021489606871139015261055314843942973293904839522166441406080281275771270599523108742892246047113374593464981523619345393153978407803117601455460467896263241609274393156297516146653742513445038144711545760934898277191190409964885745786) (inverses := []) repair4Step37 (by decide +kernel)

private theorem repair4Step39 : Nat.Prime 9455661739254560557764390254045307346778626272481329655797398651920363070919446392521200279477301954346402599736738165062192629356682802119431280721172780702692828284817924601099690384789587514285031044823959211173157784558294667095616715866275926780743243536815831709081454331890610505371633792535302967840077 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 6157737629714163729322222390342086833992147753926108010137126691649368981547998697064134731745635007939000004457217863954211115935902272604485872017579680617702123847358686160773897241411337171413169359461995258336974485064641584623077475895213980794023262648049137796452716546803793918566223799305504903263774) (b := 2601640681690353042927640034387996054168014159548629343749853325721055487683433468438863484419555313145185216674415907000752916937305340294318162774124300541226887700335968932378027046996509387798253260615559773162899521459807260675888187034113805522438594898658627294569618395282103253759588845849800723670688) (x := 2427164467427676891146459933198761847375415017418246342598170954336518472492851244439074363459486610158318639339217927081065850018403790588031473781142244848950770277525372177809075077311621286109997563646655780693430609651267352566793367834161206579847838067990948472527826075523835555987920122039778466293502) (y := 6125034762878298072412765135624581173652187779178067135336156386205018902321434022062588560767334005998056770170022514705602910454404073846899484930178601659473997802128203706236524570566528562750579685683519618787392769736388060919281178819401110644441301746605748738791373591321276694389529169581806075065940) (discrInv := 1373934258406355920700395634836648721739565855181030612799296395492005407807710411148336920824289510802137295669721351370935998644554827084693427099477266187060498188304855117305683051607361005878906222336963586638148014947930555880142910293171077494045340573361768076288593677100036316330743718183400033719796) (inverses := []) repair4Step38 (by decide +kernel)

private theorem repair4Step40 : Nat.Prime 1320653363798205963981836858001999986509877174224922350365911074916413269389177238750651000634035809359653358300030746037906320156989173606416728115764759935203700096189112086096547163893904581852259173992311510157665548119212496124461070379932267041192733374699580310857284241911995841691282988303908685643818121793 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 39069671746507224358375501852130372103423961433214455164908560309680006005066890947804667067424442432485626540776961528901679511295203675010922604038777717591833804459082413476362263217757418143589920696985631552741211604886114573518393553429208684400826394035575353234982797376405922501648943424423546292175294002) (b := 2158144678158592423973608814270043332320200634761111535939575161969549327995353337345819178164151800205500881462622731458805794773506413712735146347155891853817735948975809465698239330344850041163397214007747799260196442071301347771378477110228805117428299269516439394317582302209304461516277894751199337543608147) (x := 182218462739048247462904002016741309390582255608881711721412687728210041899585089630559211481770369379986407523206363537259744328873476294749202901345238620312795853116352640672913602166678595028734860618195628958850545759699159408095955103251371637721052121713157686769361787938560548718387805308975176335683678618) (y := 604270028872055582305202308175801944584374301396191614671346681593586283698307641817112922692060821867549454052776316254681715480739549112205648464827235564704357477184085524951319715631740265291783726403580770368615476362575806813773977430031571014294869322668686295978705956859716846456478693152714747410288139191) (discrInv := 239907227029146548430711651606426593411612393050052102933790940227953310306311288743212653884073369353183144667006742801020950221868165099450102959988907004282367455125601386097319105692549605544072499729857889707985449738336665707455856693832387625562261365869222885862882891709978642677310883998192253828468276842) (inverses := []) repair4Step39 (by decide +kernel)

private theorem repair4Step41 : Nat.Prime 6603266818991029819909184290009999932549385871124611751829555374582066346945886193753255003170179046798266791500153730189531600784945868032083640578823799675966157645942302575010658384513667400947128149307711538532952572933117299547626569487668858486207068547277419368708567645774474101460449897549454832410028850771 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 3995869159967674446369226876847971846610363902498637162397249659544022330412597503593788098168935997506939332541913314513457006139121162493413389378806933158521318821458879247463055172258459553587329742796259238802253930390282242324556952402418506651605731187769576109559503577375896395542808686489484922742238051792) (b := 6326420391226111564326287081738436775969766813910447575527990205999481440245865328795066820812670604555127653981686708944769423747035257213279444765595168639118586080995410240613556645436962686104593800387374899977715125430845794802361472322569706234547592656071561548455977915867672734391125447404190548064638384055) (x := 3972779333938783478267248176395036206718846325392631444710557740142700879242455273283773167207222432372698101981095575332492153766673345648866430200560432725173893924806492237652798412897945803900304102363817476681485854502299945493816070775116331601419351305797643678294674232642849022129548583696738204991772601836) (y := 5302798149401457444356650676786359413331596010135953861100905016921503869830708041710910606116621007324351456483772849170997704709364622645034716824884211615013466081246670813958701548429440431630716350059448737803572148709073268608121705945096743153202227957162792726794091411659093246683157057987844471454225620714) (discrInv := 6559337930653316207457640461973142077327207882808278914614367217772005976970029547514676995286877187785588165420005269417438976535508937967163488447596213013901547969487784349764150693304850070421895560357727800128702599571041467804781522083439599715741547726147465563744638710697847743084744308988069110071888435386) (inverses := []) repair4Step40 (by decide +kernel)

def repair5Nodes : List (ℕ × ℕ × List ℕ) := [
  (3, 2, [2]),
  (5, 2, [2, 2]),
  (7, 3, [2, 3]),
  (11, 2, [2, 5]),
  (13, 2, [2, 2, 3]),
  (19, 2, [2, 3, 3]),
  (23, 5, [2, 11]),
  (41, 6, [2, 2, 2, 5]),
  (47, 5, [2, 23]),
  (53, 2, [2, 2, 13]),
  (71, 7, [2, 5, 7]),
  (83, 2, [2, 41]),
  (569, 3, [2, 2, 2, 71]),
  (2333, 2, [2, 2, 11, 53]),
  (3761, 3, [2, 2, 2, 2, 5, 47]),
  (4649, 3, [2, 2, 2, 7, 83]),
  (22567, 3, [2, 3, 3761]),
  (23899, 2, [2, 3, 7, 569]),
  (27997, 5, [2, 2, 3, 2333]),
  (238991, 7, [2, 5, 23899]),
  (120929447, 5, [2, 11, 23, 238991]),
  (1069659194913129143, 5, [2, 7, 27997, 22567, 120929447]),
  (6046980246135783061141313, 3, [2, 2, 2, 2, 2, 2, 19, 4649, 1069659194913129143])
]

private theorem repair5Base : Nat.Prime 6046980246135783061141313 := by
  apply sharedLucas repair5Nodes (by decide +kernel) (6046980246135783061141313, 3, [2, 2, 2, 2, 2, 2, 19, 4649, 1069659194913129143])
  decide

private theorem repair5Step0 : Nat.Prime 569013123421822789293053490475613459549 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 569013123421822789293053490475613459548) (b := 0) (x := 444889953409517185072325470230941388763) (y := 131509583236640845642455809899626316467) (discrInv := 142253280855455697323263372618903364887) (inverses := []) repair5Base (by decide +kernel)

private theorem repair5Step1 : Nat.Prime 41698325254419529622390168286956816837514741217 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 317171103185204387488870917230978107129022864) (b := 0) (x := 8843322920042357359199500378672399984270480396) (y := 21604267718880237661417959183383907648636555082) (discrInv := 33065336246460821610236874962679543266567800814) (inverses := []) repair5Step0 (by decide +kernel)

private theorem repair5Step2 : Nat.Prime 273750631150046081298291258828019222095385897601811373 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 137592767795036694009864149670904347615916515200228111) (x := 138034264407141417735079029600153563528208266551494434) (y := 244535214618889096202571034453831074924240859301469812) (discrInv := 47223040857087104879102202220567578561252155826388677) (inverses := []) repair5Step1 (by decide +kernel)

private theorem repair5Step3 : Nat.Prime 14927348165980862767114524052810168225595476412283638988433 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 6568707399541781133802304407196563817142453406073348714597) (x := 10829730872097233995280873453959108723036632813883208247999) (y := 8412973603837678136004428596868965494227082654818669721272) (discrInv := 13938916558438156990864722116792404631861324607958436189754) (inverses := []) repair5Step2 (by decide +kernel)

private theorem repair5Step4 : Nat.Prime 1667280298702900505047322535030535014738028775313210095179015747 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 600851259610944666991478630566593185272445896599256648851746808) (x := 522520440312956603529692254846619603351539517152393281632464200) (y := 972518616128769060565267161183553540637237775307084908168345535) (discrInv := 1533121788806524053911040220990975925381979785823428424488410449) (inverses := []) repair5Step3 (by decide +kernel)

private theorem repair5Step5 : Nat.Prime 7127623276954899659077303837255534491367930669116619325609108950351 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 4168505168376775488354061350406731637514778032153080767244800961628) (x := 4997501391775936764610548907864746195574234161427186503400794737424) (y := 3811892612636813519909528480921055591793049165241987791235297806831) (discrInv := 416484839437364682383826989953883282931682543507573121490272627680) (inverses := []) repair5Step4 (by decide +kernel)

private theorem repair5Step6 : Nat.Prime 691379457864625266930498472213786794857327339076724324999534823642797 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 375102883290869519360790565192413898939723072859344167884244587517354) (x := 454700370720275447736235368705652555592391143308762679548437629862911) (y := 191026995375093645683839406489418698028698771144896020867637531159306) (discrInv := 630908471619543014677008611928648823668310085376024776770482332309264) (inverses := []) repair5Step5 (by decide +kernel)

private theorem repair5Step7 : Nat.Prime 1942734102452667257933417946513935852487364807723803160080237633732484699399 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1544440055222940365849051434934183357670135132651975707562251176646363320108) (b := 1126859980833742400812344026204680419400051243549627060194468244797591355530) (x := 482927399508841003186216827273320551736133468155151436074031772662081088919) (y := 1534503016625289495357583487309421806575813929479406280007564492242244379306) (discrInv := 1900745442577597871649446248054219398422949781863575570506676875532973860282) (inverses := []) repair5Step6 (by decide +kernel)

private theorem repair5Step8 : Nat.Prime 71881161790748688543536464021015626542494261679123347146342223412769420951427 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 16975091381973503365797480875970995590252129083133899665121375785039325693615) (x := 30126867289547129646436732985203913373611564523328228604432567540790409291458) (y := 35645532588858391771127907604411243139481505915281766076735004977971601133107) (discrInv := 42841008289543502779681961483800557986021037876885301227239303964493817287835) (inverses := []) repair5Step7 (by decide +kernel)

private theorem repair5Step9 : Nat.Prime 52119012854022731328728250080166288939356780962473313036844970510295839835223192194903 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 44882750336645217473938113500754818875619052986509836705899253185293801624753444328637) (y := 51998159491784631644868367485379513673256741134544867120719048830314627773123700488283) (discrInv := 15442670475265994467771333357086307833883490655547648307213324595643211803029093983675) (inverses := []) repair5Step8 (by decide +kernel)

private theorem repair5Step10 : Nat.Prime 146906975508415354409853730120713355806452989455240129471685222518937782303347376789024763919 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 20136911265807606888518916870220053603653139626447606081122518118230610223733785292485903888) (b := 114449096624751434420344117284780054386304149616153820913960674295329840862037358983176744239) (x := 122557238418173277155882653658213076134996215422522416973708737002978205921970196485744529406) (y := 5156576865118029988804218696225461810533385867056455069051439192064724237755400542360290978) (discrInv := 140388516600039745945207709638135604813255065439238632605585482626255121532297112747500631780) (inverses := []) repair5Step9 (by decide +kernel)

private theorem repair5Step11 : Nat.Prime 49083971028969704554002688893012263588628847024821394533470981977367399642351609390979399136701151 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 49083971028969704554002688893012263588628847024821394533470981977367399642351607042701443577277151) (b := 49083971028969704554002688893012263588628847024821394533470981977367398257278207314892893304253151) (x := 46423239562021144641412797715421764253019236586257480973234434746766486472175073017520445294539020) (y := 27844280900790492263891961521138872734089583817826623944150739544295666822407604313855876774994836) (discrInv := 38778351726022325489725023627372935320025082598626681741149028576461986506975903926102625844215663) (inverses := []) repair5Step10 (by decide +kernel)

private theorem repair5Step12 : Nat.Prime 11136416766907791417734900069491087424306055957226602851548445876985605932473027981537623507511994528379 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 11136416766907791417734900069491087424306055957226602851548445876985605932473027981537623505159134687867) (b := 11136416766907791417734900069491087424306055957226602851548445876985605932473027981536233023814888108667) (x := 6022195104829308419097491660868045016600864423912532326732697023147889495926536861715413498267497530416) (y := 850622862219749433908787260924317732595841176945600024917520396678751026297733301721699779366297496894) (discrInv := 9518931246642214392394540585981698991647580967250245301403283397268729701088661453185176013027002792082) (inverses := []) repair5Step11 (by decide +kernel)

private theorem repair5Step13 : Nat.Prime 790685590450453190659177904933867207125729972963088755898458407884695340707517158115739366187415694172669 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 714638936182858100791087140323445360556683934852208048116173636648553501590483747921166649642462274863092) (b := 562536102805491690001510460630975955614906746332912687269596259149679914279576975034930834746329329663792) (x := 276206281482641778340789137397089682195073115976919547167342762701410114882772490627283759608391824529341) (y := 781530668701774799542608358585582701174867500930270376120850830214393059951843983439984969115470714625437) (discrInv := 144378689465048163972195616410187019517498089616906484646461383404354872800585315167510242715050062626253) (inverses := []) repair5Step12 (by decide +kernel)

private theorem repair5Step14 : Nat.Prime 2362020599151771969628496769654276044917143028342445782206652601827270962721310260397033447957696577822419838391 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 947692070797726268942161633470653606965488050359819395213772185198441111053196321457190449400604565080288277085) (x := 375916106483345922684432472553282952768726707348702115224442550456815372849260184112704229893061079276183684531) (y := 1978820229740862342424685885659647591631739496952716662816713830040744249283963654468250835535828423877464420549) (discrInv := 717556920057835942258505029742603672357564687868939677033997276683704975491191723685254355054100727254523612445) (inverses := []) repair5Step13 (by decide +kernel)

private theorem repair5Step15 : Nat.Prime 151544178100860589723119744580708109445853639163943561234198596326137328393102264929948727900539928656431189075423067037 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 3902212167502900126816635763484601328137491450948679162724063277615165236580685501491095492353589674119844324279659184) (x := 13433249441285971030581521840748094257894263339585193639565105654930872417036018313077852487792439767032093560846144320) (y := 13317134511988462879387382890534291951600336009130610226105113487879860776853306348012501211433981488128056003118600559) (discrInv := 135326000099800632525944372159533048766069751108425658715832862965722360405305202459583312954205086052963263714310845944) (inverses := []) repair5Step14 (by decide +kernel)

private theorem repair5Step16 : Nat.Prime 2086756908642684803107821109553497635433353310997592317791297514878834914274958068649596147052837943616770259967010502624359788329 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1126950664018122173720910370880386598460857008332024125200975159628427680033834409941770602873428972165586076583424835286603388076) (x := 681024963978640015339842682018639092939520847764990366932088734403711834667818406911270960381130618934943820316416305056861335383) (y := 455400207117320101287650390715278684650760455289092345429305905004480897993391066509082968503570530981379688382602919985029112701) (discrInv := 1434771017611259981995964900445674131871773868038751293931000819992674418614733214135944248691924955592925168595795619844656925304) (inverses := []) repair5Step15 (by decide +kernel)

private theorem repair5Step17 : Nat.Prime 175841854504338451587585894267015102359043033973767364253679835603027193305042814881321059790981552864877894960709796727146265255044512175699 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 175841854504338451587585894267015102359043033973767364253679835603027193305042814881321059790981552864877894960709796727146265255041121080915) (b := 175841854504338451587585894267015102359043033973767364253679835603027193305042814881321059790981552864877894960709796727146265177058375063123) (x := 124160228932276937926251695674376268625997445292250385124789841358406550706694383844108096972488648223468857843067298126185730873127911111158) (y := 23614569913740625676368150789678526529072409596386701975334585815384578443455063836469476503595486978954128006224148666640696399188769567807) (discrInv := 79733809967919076533951942995065752760368342305209692806953328302135132869372450848794929812114715615860073842135456863198427481410583220081) (inverses := []) repair5Step16 (by decide +kernel)

private theorem repair5Step18 : Nat.Prime 1743479790228221401693642550095532441651152728576471722702578074105275179826724974801407416397699518378882834763854103781551303523228275914482476565593999 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1743479790228221401693642550095532441651152728576471722702578074105275179826724974801407416397699518378882834763854103781551303523228275914482476513926124) (b := 1743479790228221401693642550095532441651152728576471722702578074105275179826724974801407416397699518378882834763854103781551303523228275914482300791483249) (x := 828193214503925362103100260928496307833782195025307074192007240947605032629082678701870303858205260962702329198557655595838111120148960207083467826513542) (y := 559679415806602151561771806782678916212095511198631549406170568488095576775151694537277389593311688452618716912181389529337378250948986499576375797445450) (discrInv := 68357546237532331829543323080001294923672485036927890310288920141669187935287716685249074395467357953730578540271933078827377491507794366057522986839265) (inverses := []) repair5Step17 (by decide +kernel)

private theorem repair5Step19 : Nat.Prime 2409149091536307473967283743934757205535771096110611508789035895689039769860467627874426166969310766496388603563629687920896542799455785976834711567088447464411 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1125247586750131919037125005483168623227735686480703379377045975368461975116654629419473368502768301289803559904139348075720648809790416514512488667124546247637) (b := 1949833710435497265969973563213063312561279848286626648445008677755866110716668208590723048348466234240443071284859274208594102110357104824025387915339988465237) (x := 882496782859359493980239036602232166186591647178812099960765088548740519740782694974790221845808188687564530491144512129729324027508776152307906157794068005693) (y := 2215731421529563031778039121535240494250827767844348583455414716662297529959008310414114188332182231519074752700019739363077953328967994989562459360161225302272) (discrInv := 431258881725372309257207701591326098741997962876586238812886731237293721840939539228650233795880842324452253836836375423633508855726890458849600774176893556145) (inverses := []) repair5Step18 (by decide +kernel)

private theorem repair5Step20 : Nat.Prime 835550076086055421804854754068204850549227861451461581176497325864709989062898528005918886929256691997185548316298532279794184390064189511416167001954226263567450404415947 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 351025048918715276260708215992480869959724591758241886963038121915660162361278823760684798619564339816581536734770075239914866028371805397386273329924479283064225891054196) (b := 603019435110934740428137653509163859879222553067591749785046712187591904690402165264583949713034924020702647053412187308841305254900139460890195123043141215200954435161130) (x := 328302264598400758522265706319133630830095439587828663768529918417300483257202718286088738925078423911977001326377881182725209022719436739911351691047622104472089490455481) (y := 93124452838761913116322888791859540946648171537715641771749128907244644261133962828437652707350432493984084674812593757665032020385906650421292198315119205020010680800047) (discrInv := 463043739474047971443221962969955164320757156267800861299843873283334972171410023616773674999782627546680891993854668051097872427950405440835864397713692106831894318661577) (inverses := []) repair5Step19 (by decide +kernel)

private theorem repair5Step21 : Nat.Prime 12184826759562946216180196878576631335559389903546664238296860503085065770504249233910310364901774907011546519804381262634008707018996454485686922972720884898391998671784900521 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 4269690929582924882486273296052566818914433740562765015380123154700691985588824550873475285469283495065968026079969520269468982958825668198481715722467332685734252767822599109) (x := 2999019978250987937221039099876363202896591732779112379789356036391255421467227932341915298265950959071794414263337341959141661699543737711224486799726675070231258758581074762) (y := 10424571114439376254924959247255301702398001005375341814834294958324163823964322256575612328603794509487362900987826740200798923347074729921899352107520207495282307658180320013) (discrInv := 4530625380714543880726853003859787833064151312169897191556612468605436172092492741915098822184946844622574263086748695186997403093620339831266403301372388795026470956687009546) (inverses := []) repair5Step20 (by decide +kernel)

private theorem repair5Step22 : Nat.Prime 40356146227672477867988812061845802983372699360546551957239201986217737831910073462710947574691142488782750876539849392563263297032584652117136324772903653068030707908031059141021 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 40356146227672477867988812061845802983372699360546551957239201986217737831910073462710947574691142488782750876539849392563263297032584652117136324772903653068030707905678199300509) (b := 40356146227672477867988812061845802983372699360546551957239201986217737831910073462710947574691142488782750876539849392563263297032584652117136324772903653068029317424333952721309) (x := 28370777095583311909853475647211013503733269476746099911094388969574788011994633186344135622712168997863244296038823357154920622491711478670846656175577665106301648584937245097378) (y := 36683919775083920846473697401840181830444985346256741979480947662437214340590874733401866596262129474096256694727591263318982465664280445421955266753237670440788197390439089474396) (discrInv := 3833787218137354776325218425812713379125435252851539420196397612416307788550384552310115224315515365700048451835153465257063281276075473775813743313153961290398831174560967697555) (inverses := []) repair5Step21 (by decide +kernel)

private theorem repair5Step23 : Nat.Prime 726410632098104601623798617113224453700708588489837935230305635751919280974381322328797057833552141774641009323428946307341736590564141190251971663369719758841956022891624620023247 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 664909170342888570566498242566222183289368260877964651609806857438168238297068951012313440571818917439963541918925551841519178912236656325590192934349336579546514019823158562541979) (b := 694752768622531774388475363650550665880887625899202143744321585782200499498078632682584382289112252502673098219941627161117976940136001080854150589046464700007830934315861612656422) (x := 472192948514862654423710214277602727758318649314533307647332956492187527831450196363646756669713938441360300395851862887376351932440773239366932635815662543347363445606460799454588) (y := 691635516403880089587797737097492513833479979540386516615493677732227464820004356141138740941695054604911707280819457332767566784934799567024391125878453881926487886082730041000147) (discrInv := 76042489331762338007066049179557280190033134129503376237069902291680849664380635718158524450173980326254944484935400431868332098896075734145885713915333586383086585956165467107745) (inverses := []) repair5Step22 (by decide +kernel)

private theorem repair5Step24 : Nat.Prime 70965259305932256280094815134593835518239203660138334550781981534209501633405068625613452478832624526219574811540479188679147551163348225178913420115167513800226202863411370518274795851009 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 70965259305932256280094815134593835518239203660138334550781981534209501633405068625613452478832624526219574811540479188679147551163348225178913420115167513800226202863411370518271404756225) (b := 70965259305932256280094815134593835518239203660138334550781981534209501633405068625613452478832624526219574811540479188679147551163348225178913420115167513800226202863411370440288658738433) (x := 38604464374704632544058001395722412862731896315821708867636184253767059570116695875127389956573390786427350759538598314228784242022564952668740197087396242597412755606212943602097013695361) (y := 33675621448343085025650857257811803971549124153339631189871738829049440331753857567024732538558760847492925411820309124866854582962017362304825327981636445498216199085691927016190935558858) (discrInv := 13054750677059081135467751069739795911992741248850269649871183126505259139645825492341974081854551357849482798586796652773894643798402626035988195967534330829465210972187994414409299566008) (inverses := []) repair5Step23 (by decide +kernel)

private theorem repair5Step25 : Nat.Prime 157096410496896485288637177858436260447759039906912080829796139854801092550922028209175663214597951947650349039790947191786185385314327924853208055209328093480175874261664560447581168859021723706534271 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 157096410496896485288637177858436260447759039906912080829796139854801092550922028209175663214597951947650349039790947191786185385314327924853208055209328093480175874261664560447581168859021720315439487) (b := 157096410496896485288637177858436260447759039906912080829796139854801092550922028209175663214597951947650349039790947191786185385314327924853208055209328093480175874261664560447581168858943737569421695) (x := 123320489297585506186115656193259311945790792274024077429501946707457436822014793650660639520526085737996919699584357168313649611383104968437151904382274209055105596430303725531255446296244786953393526) (y := 94967498086866374921382543179768115602458122205811640996117902163212270335990380489965857412610161078748751277884344604499717853588599521742260533566527668429885899746576412287565041164312302101539835) (discrInv := 33441115239018709604895344043747784000024989400944690675216767291103794687144608467382752001419146938564470156811152457206689751080103996215246060199871844176439792434625666078738368787640250628782341) (inverses := []) repair5Step24 (by decide +kernel)

private theorem repair5Step26 : Nat.Prime 659720580909326380452082501168286233753588691153613197271891239800230224264895039052656617597839439114906586522157070846018662782168134194406737302555490141474218994775234678960475143876140619017541844727852493 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 188108128941259828535001193506710495000893467894058610899956171026203091087439171359327749293052644805278324072435611835699725148428475189295951707648384146533623859423530880931388929225558713131677312403578202) (b := 94114163583979732174067715635280774530607792302065628703902683211872969757756211799023337554482125948553282651885923016150740663401495553318427888359238320667294280160923660981063267408517079851541527833332067) (x := 29943403226304204302174819011134314385587299639990435750029285820846966851549027228897495276262818773199721853184340547773745515898681773773280563630625241200511254943713861794035260098497811405440226497880118) (y := 102833936652345077743459143603172106790730556177898302896724678623616392836120810432142385191036473667840618460933202006886699207602332160107386034595328074134753575340767319898922517848389781229790551050816109) (discrInv := 115503808883752601103826514430070717711319304598358302441058522203382127116054369769368767239304599614942252542755249519021965610507802767955162875763193803624096269058289303038338603641541357487673641874951590) (inverses := []) repair5Step25 (by decide +kernel)

private theorem repair5Step27 : Nat.Prime 73329262009233445840009874169857351454178890199106414103165255086275189887491613380780888359235049336500097309919686010483063165095240687290202455289540568228796795612080126922533014924809801993615066198591075966689 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 36785837938815230332067899390321229472123243129339018772654753197787377243655956024492855011297609783199323623965154054791652144602338971882335271497813485478718087907087348634406915203574190153971563259571885197006) (b := 18110070966934237187557052375933200448799318893949617371058906538312396600411497559352483542156307698427942965060930611867913377649046140150682027720180159730019762576870586245579248697963874037050339311622500296660) (x := 8522949869996307752614817130370663731987009865086017966685104505739654097448509284514395732818033606540595878788625243319183664853565071756963895207316183987858467604305955174154455410692369086920783479883450803776) (y := 7579970099269364712381714341354023988943516686065826786325990645999021766148433759984052868592215855357761956715689624826718392046238555609350248681838454217397854196782120061108481671165254770072466750732329834028) (discrInv := 55964860197273089945513469054254849395831023079880285694634081780196716776654992623638023001571156995980943511553077272702788215987544936934095117717668128535283763501808033759632722774242112669944993486078435117940) (inverses := []) repair5Step26 (by decide +kernel)

private theorem repair5Step28 : Nat.Prime 176785534611157541888800030240234767079635976142589808594349105469437722283925845714676809271621219118588098807928116442856220566565025046099649901950180745262805158051947314579588346288748042296740007892696593157965003494809581 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 10746083716260954864722627971504412480964264324287718760756792587468512930532882372383768895633207812213785052663206636430973757765670321350631982626490854893538766960282981179170496745494567308086335561778677493201484031466439) (y := 128666497718982855425012854516275512116810484896876660582625463702636031001557994578258150815509315787421494914108827886156693793829329589865573036449752738461646519936027085350890132692037648265149534732573402532174321894264807) (discrInv := 130952247860116697695407429807581308947878500846362821180999337384768683173278404233093932793793495643398591709576382550263867086344462997110851779222356107602077894853294307095991367621294846145733339179775254191085187773933023) (inverses := []) repair5Step27 (by decide +kernel)

private theorem repair5Step29 : Nat.Prime 1174572284804330488501365618517692284684989566562126102970902362892428637615962083072289883994733504127293495061012415800876828096548004236072369352775694016929457204368764532395169094575942646544559953881950685838530030308972311936353 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 442452288156023909904576634897713676452026997010754763588006729515318424506713173645104051423695448493790621064802392002347465624294350988737465035435784075419196502529262101812508943687842596201400064737816919569793833532083222192169) (y := 384997563858640103883823302527360638439676377388570169321874575059834283412237633723632523449942533467710701428196329807509342106517848294422323911853331304794179555525671141729097427827083693671843278745183255206529711513763892390932) (discrInv := 739545512654578455723082056103732179246104541909486805574271858117455068128568718971441778811498872969036645038415224763515039912641336000490010333229140677325954536084036927804365726214482407083611822814561542935370759824167751959926) (inverses := []) repair5Step28 (by decide +kernel)

private theorem repair5Step30 : Nat.Prime 62751686406646659345792871357763065750830854122141772624622668722054079119784765290904551028422628731224224540136906733860923270865214080252496975158618278288723549930595858696463761784722879938316745080188860973027006345129650981428950493949 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 15820512004206221133748760006603959737404073318493472856667709313956360514028558320946010036558279716009435396065718169198716967921159132310424857059149932337455273433885922895456893649254716961683514544866179211180445870379808372086260352136) (b := 0) (x := 1846383244861200701173772544903840246123982659328966124668565106134416132220557619769336204981914364029275824388771127999552907489763557005390659383189560233962899600946910168679090896807950268437864329820750466277662530763338057040549537499) (y := 4631237270973107824649704754179581976498247340842491779010943665400348047086958519092187830125005879937217818751780109948163823076263478716780969831928251025322244624955972400585702427071823879960879201556837596541430230568610328881930504535) (discrInv := 3955128001051555283437190001650989934351018329623368214166927328489090128507139580236502509139569929002358849016429542299679241980289783077606214264787483084363818358471480723864223412313679240420878636216544802795111467594952093021565088034) (inverses := []) repair5Step29 (by decide +kernel)

private theorem repair5Step31 : Nat.Prime 3467573099544526982578441176096425886673754872151364730992969685241921306828019701833651023259439922602891108039489040467623445315024492484874012247490354512504404865210507288585933972078821663198307758197655696800509150845391838885374187136930327411 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 1593217879098252586699635753953327514690697472185876932446852329311109976964981576529355049146436645811077005616741836414616082088927194914843186166985950592279036375431532242041811622528076507093544688491821000439343250456099310723819750872067474993) (y := 805752636906544296914285162524716445592008853158520754285862705685830004982823534080791446252873761023195515032458022827422492264070891022118335132585055474178006679336941181789194995865989669174474346831597649560398139536498541173458795227237292244) (discrInv := 1412714966481103585494920479150395731607826059024630075589728390283745717596600619265561527994586635134511192164236275746068811054269237679022745730459033319909201982122799265720195321958038455377088345932378246844651876270344823249596891055786429686) (inverses := []) repair5Step30 (by decide +kernel)

private theorem repair5Step32 : Nat.Prime 17337865497722634912892205880482129433368774360756823654964848426209606534140098509168255116297199613014455540197445202338117294850903484403559171529477012391421844870452208167333505836258451561765927151619161375534867131326280955208735311261374566207 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 13732910911195821956067618324054570100380078121810362282613980836340098972299749397982197369539148802323078424635119614935862621140131389209790268672733381676503324774282532017781952208106818622206302945760612629873002893636621358925422237941377087175) (b := 5771996706949503413062559518100929958354155464934998390819550804827934615176115478179998216022705807285329897170381623241604877108332556878337840181593944889413057667720840432197282656431229860740625652119589868850500059879562431449472760657157949945) (x := 9380967261806573035446530690792881356520867241802063455121069257957377368722695995901307449771735896108164561565366252469846905380503324383386896183481524460528851448821981946042063211344183218621470172206177718071105238558951542808786924095610518600) (y := 8623595127592743850115372172151296574078507085409683529947100056772909239056109057593912957743676092159805218453335994109766852406209760405102622509850088314312573195511405233040159987562093091482453826205793975689293732225439735586026099416328624286) (discrInv := 11014076309579292327608291675347496934881208647177608524873142292599877733519461940835189400566852540896482641715057058614364295999034425185570551627881337166838157651634223503236668371556871224036908365516544724592018760506056823077986190077997988027) (inverses := []) repair5Step31 (by decide +kernel)

private theorem repair5Step33 : Nat.Prime 34036945299743599501501005540340589845651733209443715149413151102406045357310115295797927270434815472511917739040627471421393875439438096121259430520615417955123753779841482611564616577917997459247809698194840144721370378883875806985644056857889700131574525820217311 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 34036945299743599501501005540340589845651733209443715149413151102406045357310115295797927270434815472511917739040627471421393875439438096121259430520615417955123753779841482611564616577917997459247809698194840144721370378883875806985644056857889700131572172960376799) (b := 1390483697106419712) (x := 13228104081385117976797554636066237506711840609672564610120324426042257837748364195469378316665884634860647193026178091915244523511775155229161056026437017642204974566180343417485583805711947608701746150163254704002326906361267342410158019275391289245734877955499277) (y := 7090809257915236743495793597195723050592820726737077995233538807288020410178676116887861481820445267599592633632514849753962810819347635199866243281100404577712819844462181851582522901448557647360121789326830752338126016229750886882132068771891860917387068770754803) (discrInv := 11825856338956034470151942513669513125807988511483762875583398017152747097551818434300465168241669591707099847735096799176177916436813272067150521762546535544038578375868275176155057249445558713069846474612545086047779801117920462435064309636098101915999952675141516) (inverses := []) repair5Step32 (by decide +kernel)

private theorem repair5Step34 : Nat.Prime 777856522018630402487652929915065601919632754555380055424083566088616076364215257889458771289427968437956609665617171792634540653580110681149367334624309582448723108780608920218524757624806116680056309436971381730210357786898796574749042871484480238072351677174243687594891 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 346987224184202182211657596342261605951191749532653134348131447045367980583454420582872227887896750861517405083255037312629128715727401456680104976499767972602892191588761107866707739355142044681443042481296252358217512639383642065582807274421209823114843780316723176351748) (b := 261264926942016667411775862147057588957302806276462745259470497399727021856515457963912592687094486240198884500934819849396714995185772983260558529951253545689529381477828784620004319097854773728828524577856039714912171226310706465979814593193087057599201262016826077185171) (x := 124636183265595670131763501560279705720729130280001045305786098859856232075386597314864992924801743363097476618529435456294530287286082969397022847386605383141508907510707713635380061622080442845113593752629890402593163782173179004385912684182191920357098617568588181465380) (y := 560501384961510884148318311215434809654135794240654709719673706358143078633828791061541142275135378663104120325107514409209354042055624594287246996199464763537595301232853096519121358625051448764289148366647741282703441323222376193398782532914373891760480639509280169173868) (discrInv := 267830048672019548128830773387314300245309302150272725398435327536592945529496103232283062283345495484476694224582794523249198064610582891535785330228505336518165271710582374820892644252458615392971281893117353375322406996354252777726797872602018045086830946430647573442297) (inverses := []) repair5Step33 (by decide +kernel)

private theorem repair5Step35 : Nat.Prime 66386942728202030330711226956531188861432977070283466210223836031399027653380315399833748294467519394305844808521763143814187506620448126206323879892365649041764281040416238979340094031004091863063899663558298141633084527106248368243503012319071457714551952436689965111027755031 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 57839619675783010052818787440097595712940794087582669256625099317690731969259977516600851679847974443399975500142722662690939348177044836523659355858712458769894000063873694973724472212057855338414544790130208617619597537564346054774239893702414533643189392181867701142495174824) (b := 44361978381777572633117943859455440958693844173154300114418275375601690578903527341784972657004439393413356125439744954948717358427508119015343473024325183787679418409091318157871245383379310712956265166709034974921809560826396893258652185572880980270653674369703920288071835431) (x := 22111009884746181121047207111525345101201320262242568646537726203114491638364972316538670400373498861640093367796926000796309336148819422551309944042813133080702127443838983410426745965563135407568521490972917932769207811242079458938306980347667131257468009805305441677818059569) (y := 59340010575710296898946315417284311207880488034409905475253862687626459824655242858111802699296024116068493668065161540621219473348521050561529466868325417292500586267707936336935108765961840964370390884987864398568495753210663345611007636300304403707926392919108974404609072665) (discrInv := 21176198849892619051297918678802962859771685515461327467774870263042111730793339579121581590975047556225928559146912166010956573189189622566066008753845860283931593259834815034362527827989440601809680054235578482001070195185432874930726338805748687790703169122610257729937996233) (inverses := []) repair5Step34 (by decide +kernel)

private theorem repair5Step36 : Nat.Prime 132773885456404060661422453913062377722865954140566932420447672062798055306760630799667496588935038788611689617043526287628375013240896252402015352845326183155646709436428610921544465067342897594472796684342309009449028988497714680433000699949637964050968495566472650584455622019 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 96976022075378384702760603679665373661726438990385033555378840638383885586171491947759106658435323013852671062851843418474475293422310714810432816889715185541461669333625180669519345880802833874375480224895400638082703842060719444066979208329481224162371082130237748392911704015) (b := 56015861212686500306370793655046091882742228328147764391398964827811543065646185298225452017808804863546510907546837445482293128550025316684121293811036808908539031871949726299034630037839735647174642773013481492227881212492892127126333618693512257503785290745473690518282815631) (x := 54120004164730476856772843790120008345286302245297972539040616804031600589380946798768021409544493853428401987098365202948015320056614913116229962631496078061086792185609448076151192979116185463557251171624908359994517898892214996501071631858653022260620984099144692459354316789) (y := 77766998173090154885977859598160465249130007324881915823810377828381106907720148384319888205242758259615310015274437417092554383915919696214593539048460526530051642923117341619261814812348770279888292885328721239927910765455710146084544681604455323627214666421115034878403382033) (discrInv := 15368768576694291865297618259222975645117828343576654683963328647067517738104865190099435720263421660563022432837677310629983276582554685162578496393142642402483782389680294556350689391148104504716775926920655442963316123240781393341932359888707324202699963677056562486442836369) (inverses := []) repair5Step35 (by decide +kernel)

private theorem repair5Step37 : Nat.Prime 25890907663998791828977378513047163655958861057410551821987296052245620784818323005935161834842332563779279475323487626087533127581974769218072701027259029690721451981038055942351529635185550456709292415209958914117395844297771517840063966699469560999491775698572482129913901202871 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 17667716851274583321803861034870122191525323929814170420050074500138975968511055678230676385461963679187541597407331516039447156813820727986336457756714280471365811997754830667685559671000691825420680993222803427722883415083906301884566132748080503044825471445321036038261584544350) (b := 22740918100393284319291275585608826528779056764372084668280668571556103636807088486299140886354637283563442531036639319233601312990035201864876888743419921344387650395736717687068602399344192308730474610378289293499003320384227380399405718700506267391106126421850961186160576321638) (x := 11580042639364907972639667490088914643079036382820351943132703436601121110903754611851222039063986380498562114044898749848317847761964507411656864100324145988687362469419027116924848992400188374450974247634715871328371581925438179231628924671174719032223493026430795867679289896200) (y := 5090941368386576607787120370824341839405292248333700765521631572507888864258135463753806687264660584932480627405385971738385077727138205869624647757974359271699310425104595624489925041631090121684357614350725104616139046371607679973513304778429756170534520915322666873048426635149) (discrInv := 8689366237198827658919547219174447159210732936575385615825791713204121886903354287155927730340689865844488907683523305212812425617750787071032965278766859338798070856128644230689660691143377322672487681749715944416747089054400866241227030886266992136782334808871640114227039985679) (inverses := []) repair5Step36 (by decide +kernel)

private theorem repair5Step38 : Nat.Prime 19435475874318645064674790773632088247291326312244264115107559552947115663298000894219336064237424100987064165182131809299876317815705836059392282394776536561960296237656151823929573121117991489178786214532671611590625955218219958191285041362936318593481717412920141499990323591620890753 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 12998317181275874137292592669961021913204655283846328678388713752015425389237968290831614810455656496064987533421098292822295798717220093867692957467263416859328110028853826886146875904721037563064052876395477448792323139056809151949503519394843263374528565425098540081113297985436202512) (b := 13432944516382196877717362539841436924077718694148963034257193020784529345823256989008674193891628783600796262826579228219741367736590960976609556545747584168934387623248915978224935713199887839415112584483002009832297052770613310877199388015014589981873497198374828016610228934253090028) (x := 8958003243330912583985590637108318567577623355374057882996170848375774798312878798217094074722615309722364907452406906527699813717540831039304994858143707760188583176877821449600104424913596876374849838159841925901534675576204318804481808807678055253461236809303439010242650193231000365) (y := 3973242610768875188984632566159487152439696341417270500139512823315274345673614119380333837956764210793944942074459426761658874696309881897754788515925300304816105004377394004848332359791050655645874376610484139873801110710791638770360580255113340421118810516965410841589450395512566027) (discrInv := 19019615002525359864952957683223280699300963328356931167360045591927331347172351614879843716234922025074397475392662686821052216415826372509396606017793529583968875288863075483856577265457107098509274605587389000104477635067930145786245704798346033563090754000709667995678995343740847774) (inverses := []) repair5Step37 (by decide +kernel)

private theorem repair5Step39 : Nat.Prime 77741903497274580258699163094528352989165305248977056460430238211788462653192003576877344256949696403948256660728527237199505271262823344237568757263718652400113033331307203464998141366276460802682151333751477236749831960790208986293381675387788158756757620627713071808627831044388966441 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 77741903497274580258699163094528352989165305248977056460430238211788462653192003576877344256949696403948256660728527237199505271262823344237568757263718652400113033331307203464998141366276460802682151333751477236749831960790208986293381675387788158756757620627713071808627828691529125929) (b := 77741903497274580258699163094528352989165305248977056460430238211788462653192003576877344256949696403948256660728527237199505271262823344237568757263718652400113033331307203464998141366276460802682151333751477236749831960790208986293381675387788158756757620627713071807237347347282546729) (x := 58997523240720550282517857814503403047016464530350691586770312687572080267959253583425788669463793786341491499638203764952318650543389114048924946227147703720044127250810381348605410739425507921822820953083238193817840033281349347708315308173437317881452955134816344856912338951883797567) (y := 62794776466499482755148497795022325302767223026919200973032592039071697284693616857545887838198249119506970212282499622603303352680234203710158840438818736435755947090495463242841875679603026057147978552461684482843530514640351351200437330520553905373546765709546006899686340821766427296) (discrInv := 30145207602472057331936255718516598135202365553845539595733158955818546106315595143150177745818397032383572556667778351529076820806414969938751898047743094660635498423015157080049615016759987279795383349450303651681178107347886259259024114472772935620658080120886852354713501877241698354) (inverses := []) repair5Step38 (by decide +kernel)

private theorem repair5Step40 : Nat.Prime 3243331264253953625122006264159856776479233029388007597516884560889056619736450286696518530562043885410740572452372145170609395504952319868089486301367617673521894775997151401458181471732490624889422535537010204353398062857712682900977611372174062268467947105852096159989732976340507780296893137 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 33128261083670283484279320677866720834692289764651590121600679448941345499788625815483052313174353933304609922808826106286776752483833488004892279287751004699198145247692431434877997707777711868797625555760491241790688281839560340479232475489907522628410765549675259332303131405824615701634941) (b := 2287352901735096560082474517358308431181967771043968272583418583547382288277806136544876187489966459229534313997084220383227255467978857259425886271660430209511135077754936006808246626969992181136800489020784863907723672988747346554017388499975924230047169095253222713672750882843682830825714109) (x := 3119543724702017624315904649766243277901092681228452112681321627959589088496040787624429824365350045020694108317147969220001077235724994682729020918180985754279550155724063867904984477821444595310147616332658498877318405578349372963151134042646428534239292015307256481195034003016398291724028193) (y := 1592161884798940442197119063190467326616428041007798225862956865122180058951379395326014447883670037907305404474632517385426683606677898175636213575125823998900206150985549646065418887728672078324301804942998155419121115847550663568246124446509803998760890220046728029022636787687881087795391816) (discrInv := 651424534229601025712456982471378157303307756867741560843191745872430987579957081522510617950719358043350475831621698309891081996645879894231866011285744978639221375869496768211798878403888714489412208688497985574883336917409231827877039924214110174535635579670356835983881336570772712818155972) (inverses := []) repair5Step39 (by decide +kernel)

private theorem repair5Step41 : Nat.Prime 16035030432111124630409738494895609791524110499057847557277027162479946349344560643663446101188525204127654013995604666007410466180800952438107673364216796760318745700127011172176564147466614520738944712725460323284035155459405053401477406685648113410738082674332184607200824775048583447472297703097338909 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 12182531252934962773167900933392908367897938422113524790694258599554318409098954147939541883233023743059526191913246696570593135612350495263110554566578207611218877250661987342118750812962064500571102576336817079265647872598655500327524421405890720942211412650729241079243182782034997321997563538505104774) (b := 10721764391953038615365767122344598016281743610446277618277665375162521636457193614000060390502695930930651050263578147663642503951214611926034686246486930430499732655291789220510621146881591826869700467951456978069470955706538886931410648455522652464906158638342609443297581877162575807555882264305860324) (x := 5938627688020999124461493851469906179925358172227306256593485822009939996587969269569731107705020121929726609609094285757878082587288560400021517938024654485010888355183904300862765679073749474380666037558590219010433397431894509481263122537034654210061931481063780080297980221532396937870775466329369725) (y := 7953869605455662452154188222599449776477161165582919740273013987235819974130855114520464210700191049149416545252642392421586389718858979615451078755029792221064188452355039740282821977058797085513832736551940863088587967646719781638664123163032293614443533442754538633034347306017709764163730912530594087) (discrInv := 3250395718302920478543317643166617004277561745716419738697005656491391161301398222463522229989750537243279363934587881530081770190796681360344025948053397756744952932358294994157891973656379169043521303769884519304146638667930473831850367336703479232129663957145013899204945979604079831657333031849807033) (inverses := []) repair5Step40 (by decide +kernel)

private theorem repair5Step42 : Nat.Prime 75239585828582251101933205375487675159399222807789731366102824128815566740340896796758265459442899151332982292124190209444637396824020409831041263067251418113203247753395012349885822230913231662609513401438411175164474628877185586107725424367586667016770748281622176609448821612379668656257327812186632244038419 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 28673281265239397936285124200880386723560736577966999541139195797912883466966946717166726734460495269021683595751393510469214188415302273007803432842767140146258604336993165793825920942293503679412396061298138282902115750317383099794499947756576398541872644983747692823863195126667027116001482225564649419326227) (b := 41201049534962224646512424863924031690697382509359568778659832092056701909538670273843902643829236103865710827304712059028909131165822840283539545582930922056749287646144470966548047419051787618052349296526510082238545683009878603496642173469311495232667195862379295643937611302644585550516829467260107213300864) (x := 65610163709140335441888068092819271312211771446822856300932112288923777320979402890913486199613088314440258227768549612905774653378143810748092072376807115169509982023332636781094854043422738539991507496567643239753191895626706731950673342658352401433789402387287968222592563859443527876332237304088725332515256) (y := 6943406486346354326642875434388704777629291818482308621386977566145354710219969662615330363076295202444020965962736830777658744640426265934164030205334616361485614745684118736577305406274003768239130697643330599474906568141675716863383159776081139736448769581516624669673621031265185222031756930035030619336670) (discrInv := 47360704033995158483896884591928299112746326184058873588199258016030650959889319161591032892629504344021133338014130232678246381397124737889323988477092838158903937586873350452494298416998139033371330864800983979813077389064073733920099045931097571731942679475491536101590126079932790758782450578760517371689361) (inverses := []) repair5Step41 (by decide +kernel)

private theorem repair5Step43 : Nat.Prime 451437514971493506611599232252926050956395336846738388196616944772893400442045380780549592756657394907997893752745141256667824380944122458986247578403508509903970511857981353338940881533564089914321291029849994532267799696691847787076869690947553867241560572646162194539119974668408905342657696963363372006797681 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 300480118319015460889715931309539202975957914495988549082848762617501085145278906183200276789705958573829473596659734996870581152220949096466453171115061360448388597306367820797119149885425351401360238302682253231823313225367377481117085104177152881871096724755840376186847827440173184783963460951799259234218279) (b := 187885271512953904529223405101642934726508062406083699837138074976078312584564800596081521359842666056416270550232775952969640137605697212084703164209148501371637779332950776025613355375661982747299664584863281827447282083027478251332634666436928750421067501680540564898416720746026406857595111996359591772156207) (x := 322659442642505475358006844971747813559696361568812421613061014595372981318787636053204499939939806664622279263117161967546844633187541819846812189306283304691562269031817106059637628133456979117155404635467554977357862795059783458146226426258887881161245344759735764134639058770359722240131013830744711101652505) (y := 217932197645846292249887220926256186680421409158119750427879230604309660343378983656264091998477610235309031908233612163284915598386106658117589719813656827207666963662586831073614292107230591664210103477759176676209414799632327563744292543344889405132733914581672247236246433938831823746473731113634762526146544) (discrInv := 135559440892564161836946162786003020164532108603025049823491488527795267852914487267046790528592115087775681888710289911612643543243433581811213784120928743140746154925732100174535484856376171734203170373975600512166601495789525060060478067372664975567862635238554436760721540997238270945114015727891804239713731) (inverses := []) repair5Step42 (by decide +kernel)

private theorem repair5Step44 : Nat.Prime 8254083523738787274886480362512499915686732338905764689786944218227582933682357742191568753962723808497833489375192162736914500981182335040104550723529749594957697057427878218763322980642084251183910186634639423166190716166396624434533211859586073107758835684096774210885709557218092626825562371936818540512536064039 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2281950552677443524085288534313847919176280586352049756957279223091706881385008637364867694077218093225174789300691945850733417285477964544211311436825156244409777648044206744727403653588445813909951886972918308617106215443832553745808551500151355966003101690080135182904553827933763380313586052114810814455906216724) (b := 6371193795009877284392239672801057843758481307274893485238994729575403623496609397396259554426628472294518490137450175246299600807078178322169104878699713675113317285613465581711875242845107704846529794630492330300738216235564869733574987887082719163519326935131487168781864924773760650905014335488506313346616979829) (x := 6493060551936983208576958839093266398990650354628786230289884786594933574244299591853280495770513351942342746119998019850123507052767040644973994458072830465159282129273698598704149886784203935263248447672708864669955362502678410528349796925477006878776784450627539759717310278952062497246643880486860230532741484548) (y := 3941303589168215370574323943670946269628698750756363106683800128951042311575679200784316425073099799277465257875005475961746613000913065152923285047111672477930395953419044436733892513052154553778351437400498852887816649814570517981064254134082767660941524591657910320349011596732517416702678249396531139673953021742) (discrInv := 4577260732597314489504328685476289666852251310426541404639057036935666706326820470138934446869572277776906665773865215933535874886823751458961031262492785197485731670264237134203531746593995341070182640245529162455772972617384034259849724648553404225515185265099615817404836135306406977963305239854353981540728933949) (inverses := []) repair5Step43 (by decide +kernel)

def repair6Nodes : List (ℕ × ℕ × List ℕ) := [
  (3, 2, [2]),
  (5, 2, [2, 2]),
  (7, 3, [2, 3]),
  (11, 2, [2, 5]),
  (13, 2, [2, 2, 3]),
  (17, 3, [2, 2, 2, 2]),
  (41, 6, [2, 2, 2, 5]),
  (67, 2, [2, 3, 11]),
  (157, 5, [2, 2, 3, 13]),
  (2113, 5, [2, 2, 2, 2, 2, 2, 3, 11]),
  (116041784713, 5, [2, 2, 2, 3, 7, 7, 17, 41, 67, 2113]),
  (110185852089243169, 11, [2, 2, 2, 2, 2, 3, 3, 3, 7, 157, 116041784713])
]

private theorem repair6Base : Nat.Prime 110185852089243169 := by
  apply sharedLucas repair6Nodes (by decide +kernel) (110185852089243169, 11, [2, 2, 2, 2, 2, 3, 3, 3, 7, 157, 116041784713])
  decide

private theorem repair6Step0 : Nat.Prime 85824894202623744970635627361 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 24281043235011004508957073149) (y := 83669586797987234474788363684) (discrInv := 44501796993953052947736991965) (inverses := []) repair6Base (by decide +kernel)

private theorem repair6Step1 : Nat.Prime 4420981232320195607301003053158592742379 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 3995239228122622056095183603625775554589) (x := 3994667291469228184351046123705170360969) (y := 2524811385429474359617096003356784430041) (discrInv := 1657374501890185804280065992098579029972) (inverses := []) repair6Step0 (by decide +kernel)

private theorem repair6Step2 : Nat.Prime 2617220889533555799521386286345551290583981 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1741891486153398309446095280421723968299740) (x := 198729839162443608027221869547481280598061) (y := 2249454010383100276799547837555787877911165) (discrInv := 1260143391256897236806593397129339510281176) (inverses := []) repair6Step1 (by decide +kernel)

private theorem repair6Step3 : Nat.Prime 7851662668600667398560234167153752849465879 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 2644927217557634469655168418769779817615026) (x := 3357563713233139517805938188592817255871028) (y := 4204968368218873956666096444172926878485415) (discrInv := 7804012079719235536591845747777166517640332) (inverses := []) repair6Step2 (by decide +kernel)

private theorem repair6Step4 : Nat.Prime 93514786347278314242990698175411000877168762882801 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 13395435808484540260798021873302001769564813098988) (x := 15853691928294689356444125254518444531485419223658) (y := 90420677141700839708213537329090984359026042631338) (discrInv := 84447045029276798500206730459853361797027784321247) (inverses := []) repair6Step3 (by decide +kernel)

private theorem repair6Step5 : Nat.Prime 7212248690009803841258493783823863361490441674697058304957 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 4631129970154726303007678545865256578526417961462839738866) (x := 6486705962478039152081266851401452226302545593989605739791) (y := 3990282443729463892265400457206979089601518814766118602663) (discrInv := 609366946105213934438647625338827929240502179991250846006) (inverses := []) repair6Step4 (by decide +kernel)

private theorem repair6Step6 : Nat.Prime 20331466089862747214780677887981078948998949956943314491204487581 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 16132393342185180171214448974872737575313350188152596533255029351) (x := 3041279371155280525991944416708407027662846975898109566036443417) (y := 16286621977037502505475877579905461265994112358102872028284141966) (discrInv := 8446598703753966219139579758474926709643154959754088188233955018) (inverses := []) repair6Step5 (by decide +kernel)

private theorem repair6Step7 : Nat.Prime 393820498160641413550301730690193481915068269672177959597728316782453 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 213615931473918604070837115242951459338976524508542176193287734942900) (b := 0) (x := 213508791486721774976966705257318247554889807677274058262464143679338) (y := 130701976827845565215401543192675822661509610946639951496795324909268) (discrInv := 53403982868479651017709278810737864834744131127135544048321933735725) (inverses := []) repair6Step6 (by decide +kernel)

private theorem repair6Step8 : Nat.Prime 77463746879815646111789913255886592046905534617556085333767747843411268091261 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 14044239969187359979024027014944051123372868360288476116963888174192645015594) (y := 29188794534359340756717498490498391194531870008741664370429171234451720666740) (discrInv := 74594719217600251811353249801964866415538662965054008099183757182544184087881) (inverses := []) repair6Step7 (by decide +kernel)

private theorem repair6Step9 : Nat.Prime 1210939107645664563059695246352199909457645379679076474704865707033721542001140769572703 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1057928851427398266204872733801874619447737735557742594257129113705514874379387621698046) (b := 81056941894125801273122143881560883888031550794873999041810478830810363773838554761660) (x := 483676635050800057739545515439837561269789061080888249323056474509157339174955376219436) (y := 388940262566043480973464956090227605568936983241818212175945036680918727079134408019411) (discrInv := 183037375041276744082958693983634743915881613126996066020961317379709084081367761039909) (inverses := []) repair6Step8 (by decide +kernel)

private theorem repair6Step10 : Nat.Prime 18236388155985168139962033919356949441858668327662285966879899609639561396839254829971325603013 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 14006436324394028843731484588034033863872907030699370156165323783304278672152013444102564627734) (x := 1424955768303165685842957376532499441073568497461071515007405288655215433060078257439806719835) (y := 10232498727046001924602609570622163864406748415689583559967711460445061812826979518021420672743) (discrInv := 5770106701669355086629517366599658543899690370791472991929213490802197521433367531800422154408) (inverses := []) repair6Step9 (by decide +kernel)

private theorem repair6Step11 : Nat.Prime 10650360701693989941596207163481087542185973900716533349996849254674448892240735860115307073569868393 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 8713660442884587123193437742918107621654442069956985900946323722442678033843040513629098243706595781) (x := 2766085919197710912454825703418786053474287524779816372624928279144977790149451035192156981187676304) (y := 2889561054115789707538223055758111205683829231062671573912376765029978927136044131870852167325078762) (discrInv := 5413435038399880689309603902238307048274630773954958509700531878026623643388384673861402069305862944) (inverses := []) repair6Step10 (by decide +kernel)

private theorem repair6Step12 : Nat.Prime 4227380671904221070627059927661282618598150728449604170954203550293290197228688600697482950738605689146711213 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 2426549190631537075717711091639606702596569824440199813068134559784782161417324391655728029606549902295991099) (x := 843075724187753946458071633389081151909301574474914771438992982921201852644066534210772230301149381481431280) (y := 2062272011166788021904553414049834627703993305553047652220003000090324507646420363550927650678541264371058379) (discrInv := 2717831402727819321743277918977902307450424574190594768462222979730579423271584070398076645375843716040717701) (inverses := []) repair6Step11 (by decide +kernel)

private theorem repair6Step13 : Nat.Prime 11008353677634807535841115458723486522478854352191758086793156480203488999333042187543646191996330066649130461238914567 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 639795311499665663485640749688815515293100331591849348984317359785951603474751300126738300931933815126026080649025229) (x := 5417059126830079567625205039616217674163990185834576314152673686469328512622570020166502462209484568514849376718843565) (y := 2531950492389114699623577803600105398720112128345628171388267056176290241846791326243931935947202606625544285952647589) (discrInv := 5372867687822887752513999032257256771611721878373306596201680388157477164823856053944890256190429294714651166309156709) (inverses := []) repair6Step12 (by decide +kernel)

private theorem repair6Step14 : Nat.Prime 5664359393180667852374581800401628713628016985774621315317505607351189592218501407121720850708329441984424486441027775763439 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 5431481202382673094707302215647373560576945809506673590626407466125170349498406850683853957103712602437419786596408227943451) (x := 5127728822381811802406469128157390812589973891968728276251450532138700943505887064685871254864456265790508352489503136759902) (y := 760466147423722971272189069911157176256042537014575013605683966323084921898740407668966476579489233215155027807262944674841) (discrInv := 5440775004686559999059775966989019665795028728834224236825760066917144639381899612135542596589514028707116632152021049775893) (inverses := []) repair6Step13 (by decide +kernel)

private theorem repair6Step15 : Nat.Prime 80394972241056152773569691064988967339369075837256393705208402408009136786628639534972883317280309839273164239157256320285614833767 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 227062528408784523741912390563496565349294490439925499374065468702663256190697958642254053123483179427573436112706830306998693137) (x := 35073003909827424378209352168224024538956979625624086641191813683407420630948444280120208950267911738339623282353774256653537239109) (y := 31195454943280259981030629170801295899771488637212139450850655385949056321413687177102379313548274042172280055967419607940361323145) (discrInv := 62421033550817334653532096037346768130966281403129059910895281591338222111133390278580284861045545776671356652659547968034528414011) (inverses := []) repair6Step14 (by decide +kernel)

private theorem repair6Step16 : Nat.Prime 12995960477619671035076729343022224093017454330824269569530014915998825024392631617831901966835327850506510965389286270945675245429844826704373 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 11425554348130451761347231631908977139180435994182224700273510329559788750593939463458812602011014284677072218193151713974629304376982733819929) (x := 6708785209837193180866763296086527635061742285592363516991459681343813151456835786546898078560228932624693024701240970779947218818016332580823) (y := 278732213862202013601884093950016273568469777613897611395179061059076530346864835835198190691247676203523371340425273272923818038188577956441) (discrInv := 11189790415168117320129244194606628098186127735628488732602493908224914992657183151681323989797927106665794995991514712229532738459405494936433) (inverses := []) repair6Step15 (by decide +kernel)

private theorem repair6Step17 : Nat.Prime 57056709803785338053924594565639965905927758807122333878290853945923248251968170795724778429107865951415351168363161559565508133468684656892556658994486761 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 1) (x := 20585564784971380127348236590799448844683470777569628397984327081093102956645907841684056566828871975544258599171512669553345530640203007547117459863877904) (y := 55671041884545196359012116882063209095396683253086610558033067772970662991624569097470625941377062644480062347086176537328099487848576264584161046363341398) (discrInv := 42264229484285435595499699678251826596983525042312839909845076996980183890346793182018354391931752556603963828417156710789265284050877523624116043699619823) (inverses := []) repair6Step16 (by decide +kernel)

private theorem repair6Step18 : Nat.Prime 28699525031304025041124071066516902850681662679982533940780299534799393870739999872368022995294636090461010519181533280006598410438215735543989505117617369129 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 28699525031304025041124071066516902850681662679982533940780299534799393870739999872368022995294636090461010519181533280006391632759107407515289311098404057129) (b := 28699525031304025041124071066516902850681662679982533940780299534799393870739999872368022995294636090460974327930289970816264593574757641728211448648137945129) (x := 10805099062186650234342328890448395144626003934656605022545022261564533417976755076843757942931417650292714761682891440564590992084943153512558645290801196748) (y := 8358126999702334000520055281899778096981299599080501912162481498500356517535899410377890049965134756316007540396887778577772474890526256640782327880074309761) (discrInv := 13261735242889827173593488806951639572539981676569337388306732346006899125182713185425205230593227924361140192054443207016381042349853200654338771065396560553) (inverses := []) repair6Step17 (by decide +kernel)

private theorem repair6Step19 : Nat.Prime 696837038152025439161460457838157535617999368438229756432011734476125525316082581030920864232819088800880161073976324818106452795088025581207737415452780719157949147 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 187587339113722803024734974096560312691708498445837749305152862700755382607065623798087241315055237366961394622918208759657214530924302993210018828284909887170226921) (b := 145508899372887352051924781963032030159806431831773086681197376372036632412347230119616589432954237812514521794170310649966440024779327205655600639165486172681082908) (x := 82819847879930011325499191458133235886057895079918523184458444842239626393616424021442087186731727270481157879593163555777459052115655242936569069855570667893874339) (y := 240422762824874827777606448247387331843331771377978114678914530488786307829984899403977363618414826649075076251159218257028416503619155366862508225812906512622754273) (discrInv := 380719537978341492615185889460045617459014140213396181819258829541941026923009530643931894116958124620159630168963800941299046550200489415877966057216615693867766332) (inverses := []) repair6Step18 (by decide +kernel)

private theorem repair6Step20 : Nat.Prime 17008398427214636919052926854913749129364128584840311894992542415093271821914943637808202558007872782057280471262592264815137605647928229047104010408192719833334813071833 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 17008398427214636919052926854913749129364128584840311894992542415093271821914943637808202558007872782057280471262592264815137605647928229047104010408192719833334662543833) (b := 629407744000) (x := 8805169142008386292363198720860932680345141990795049036155093675976774349363712033946570498943037982788401722876987291131375176928887576217732266649519694397034542303438) (y := 8223417734889316436940523279849364104068593408378973253186888687915096771287322592449310557033690567214671804148802208370653093922200826611873484731604989175241726749635) (discrInv := 3153106609972820466756784686821805870698456155791577580720547151042016052618382784672440438228740890443186854263299637125436728089775684156548339558504529261561483734093) (inverses := []) repair6Step19 (by decide +kernel)

private theorem repair6Step21 : Nat.Prime 11579317649247724814491232602825280407271098740559284338110922876195499456359693628619829457920124712621050963660716378020946704596769872878997337534127843725432423042480234181 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 51667875) (b := 8965971106397773607630051210662718705845398118112500089548205257664139612629653435097285451357433578330589735980038320681484864294886054618766936114485274681587741292241174954) (x := 5882716537235158673258868898275750869517491868926948975314470622691285422594335939224096795056534957220230382946099019139891286919421665377444715555185018641355957776903611032) (y := 4552878938530775917334667581976773946846277049037292627361215118706675515108932835520266469181332852451246727337510129480432473053547429058705428178152499707135954072909275088) (discrInv := 10718422833941616668134835931793655901242436880036767266248636375428154386860296062243674308130972409587967782018415723226804870502395928037632261194904862149710525892558119130) (inverses := []) repair6Step20 (by decide +kernel)

private theorem repair6Step22 : Nat.Prime 33510545276922915613137627152576361498642559755178568874493010803709775426704953361225786180958353796561446945608865588238642796908987528695858192785223417124064012218453155133161 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 18609685834482262141630431355471370781032801365876079462159809048573319130871912538965569475474255440991524056330475553300257708771401976170164331069345917540132094750233307446846) (b := 27065481084360496845481448247232014622709620869403047698323336514367588842144546638851582419966217432311219281036474965941252133897997396840166995607991261924812336664654019420605) (x := 19127709636310935966520977257298927861380396334282555604443333005516673756482832203680433379212179783620195562810345017313815617343790731865841865468558236084008690614267586989018) (y := 17325923087405766483046988345734486566927244372988990946353315952393215974944448915093540815426994162902984053098722157349020136925787987807037105932436332921746940819795074176237) (discrInv := 13007916401708989630880540349618200271171366927224650057236857692413602753308711570627428906759412395890420965572226317967866227515174789412393682178225170823601838534405221453860) (inverses := []) repair6Step21 (by decide +kernel)

private theorem repair6Step23 : Nat.Prime 2238973572132327683776177420572237017170303987482500900780376023839064935359864753876939677857898909479724020702328273169688173359360151607737593415011318721628013637348799589650630459 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1125691262302800176402940390188680850493527147917053777236874389730583809426136349961043360890507293158927057793360535550188859294646313962991848129616429342716844367066975145886071701) (b := 1405910858492556671880550521537882670972730804068006121591816106715671449948679431540165909705568228958054695566577179345026193522573044022380579577336696464830468723123667891140462274) (x := 1976212717554155723603733834425215400907538241118669038895028338373901767871711202282246111004864164748678238112280186704413508851833414206520332682741443290121211075223361868661748085) (y := 1323371554113346440024095236449677173831932284533220231647477372271565319807698505838100633303444124956820723220859492908893728928649423137478880887015192317266846906038789906383008351) (discrInv := 762155102461805168544747900864932415437224904548655654712913778234430561676379499796934295268126642153015565113088056391312089481131748631345613920545436095204798559784295114374078245) (inverses := []) repair6Step22 (by decide +kernel)

private theorem repair6Step24 : Nat.Prime 716585730734523607520249359631565029582372961497761895795660126805716571626860074343068420838061412715784242377961196534673057891389062788970581726107579041856818121566001495670493672079921 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 499511958315264389939166427259966868591459794759195991179101125435544287004469045231909012984095288590147857386898821258878945755000388899646349767667175089453658138002638120484628435249680) (b := 84923043196241407876695057300659137203041277935804257033382202681732156234668779326357471401197491519425010514715285328539087177135717681084536371242063522852669604348115465922201639292393) (x := 555532111376325932634743359945206039332940977515110534241201035326730560471074628390019517469876716469890726881775663477048645372229864753822082982125482615511650165058108991994214864394313) (y := 642695147038086859768014801880726172935465760527019488832204410521837134562478664270081487383819714886405383805995983992329413064353540542953428485893106812191285093707837538523681430673767) (discrInv := 439009340551641993313601670281118818155072259644291980692115144039235958840752007258040693947760075782178604605751967033659754892269581405090276487226022250414640360846744510872543854780790) (inverses := []) repair6Step23 (by decide +kernel)

private theorem repair6Step25 : Nat.Prime 446193570613542876600203587764348070709937842443965408607500508517608314788610455050901041329552310713956544416975027936016760245520331707840542979467060640409271729466766975566564469963101010131 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 215486485568024075833736407918547932021058162387474367726732601319762491230641656893194030344209384756742997199813548906056030089018838234735491303834999672216860172900637024155884283962652712801) (b := 282733106392296442086720472691231445319693748624543975020868480265564140765009409710235972308264671677303362216322589940737706299837527705312981820293138632321395591602714537826050440815218584664) (x := 261291780779340609406293324036625359648815387532729556088820855731199536218759776988052273912342538790102258434423546057421356662814940152401507059461464408486738892742583252129546476777074269664) (y := 335627970785103201516453956243054827165285126054728273780451988871506746840224657163156699767352123573330667492385948573353521503863815593895107353781852719975307206277300131027173742435099856810) (discrInv := 394722541004468385947508794333007377213460924418144456713019575978756780251413245097573849213143378106905745099288145727606829406629402659179485729849870809818571032517189094394324594041047570375) (inverses := []) repair6Step24 (by decide +kernel)

private theorem repair6Step26 : Nat.Prime 30206492658238336097798370521116633273574099846583210145684118775716580864056012535917807858115471650368064636018471401047795156428482400951456523618616353900891042095325121347271871140852040556459062887 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 14743524189841260140555083174695579967667359797825459115396961731778542505827406631388187455948517400149455865927071473946354515630316794462422154463386847101746072426811659784890117105617499908596313885) (b := 6004780325468825265561284290443749014938210744626291627128271420062492232602643907712541545506579082566645227821884988773154001390032643154786174760441624697438386842100966905560452722164539044632463209) (x := 9801962627641713075767625680289370797929798800782177916830228601561744392093699506344671394956780711579757473386031626603449045088070811106901734448001901548287056568461492904506453861416069437461278681) (y := 10777416601220415768696030488096727437275159575088036244566099724406878551893162962335220345268384170140800200717107655936689973024835576711792935848063807844888364659449413627793845211532581389779682472) (discrInv := 29176734685971721642417726603838677130242054603153854903803247384285722227620780767902394873705732567177441057336727685540537778909297628942783568691603697192781215569288339882850235467580805390355178851) (inverses := []) repair6Step25 (by decide +kernel)

private theorem repair6Step27 : Nat.Prime 2476932397975543560019466382731563928433076187419823231946097739608759630852593027945260244365468675327198675061883475921998825276769998139574990450951578904331801852231593459050747041006424517340018346357 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 73143652236015190593274741620620797740365319756648914500465355502435725778949412873381683494329194154930304727934212217884766655296349396521583182891541599780542920008116713738495220540638581068439917064) (b := 690041354863033453605145091873933605610846809807621985487584938133132029222516399000541404484063860894808146373652412585190105432059156492233117725557015976352570683866172670797931038133456882148486470054) (x := 36327648642351037769778542819054044360491996934435743272559149357971394325318871059318830985663634663857013523903810269234342676336501785092291642358725555101033836287376712277782935625297533999178820018) (y := 987069696595773850077181122956904801617403003924094487479642811792402999744032534452201761175331596604209989065501918535661775504263746743270116144398639826532262353190741834866357962657574792248877369941) (discrInv := 2003876511423682111464849109843683401975129273482106936391187284933521051314707621566362527862325333885775799208460402474505373171427242112677550523061580560747731328278673476154288719966721610711500819814) (inverses := []) repair6Step26 (by decide +kernel)

private theorem repair6Step28 : Nat.Prime 2131910333792563193766845950507647954892654286527900007532721270350118585174168111156536425251321133850241593063279185138184696927173570947370612229529971547904631274623277633726473363247293228026296322431499705873 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1432108868176927642413021122211918155914554092060616842370996181125598059824072216929412774727886974230071218935936419892781036724327911439954162057648151831782378001723371720556642279941735192682438033493543356467) (b := 1315804262174207412287800177385858163048710909312503924290039538730941379948633722653632209564303920941960461550946738090315758693208143220387901808725982105729821431760994361757659472601500242073214979831235956451) (x := 1186988164763455827330096585610850155740342598847784758080246693861553366111421835619838505747602639765524014861875725455048868242821538226023682407007756265732606326598748727584907053119209442387251851340913771103) (y := 1973923063536197812273155484892488352661046616844905327263256300094767317052643988572173373128933897034276550473469126859408170993747757596827521171819684212295288718177402097384421834003850746352691497627573537126) (discrInv := 1598952673104860047904488696917383608662610444633472521901227089598537540235990012037773848914339095786197522512438015156997483175254248999036730587276803110226486269143224954193956796259050449469986446002988517903) (inverses := []) repair6Step27 (by decide +kernel)

private theorem repair6Step29 : Nat.Prime 289560640879102919403153228183050435661327414617626840952310383224241818293076466970383541517875876237335323489726722701768552432010540536405379631724768570471062120305501452255095619006102452028863554118696432599010767809 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 183601112907000111053326630815445765436454439135262828369180791266731332434154647943551856562159511132459551756193335358904991675368722103080021280071182078162257578462651250250967626292890725227964947581519532764563479989) (b := 5517020403610303429146035355854520873087028591729824597812680967956652231975101848327080569798349670784021094312410594607670561224247719213120857678825017967304307426240147046638868203527343522782202355570772608923979022) (x := 260043756590101633474063790822758891051575277709566807059530238854367914188376679932649608163551487427967868363131164057608448933024869623035157633781996861219575309452247941961210425703036772138887643351770241776592624247) (y := 69195315114464580552438165984543854985460592972264791743584753495380463381040800792036199758997543932391697340705365889630591485274520301043280496665168427765473808143378924622211622692375956496104340430840260072055058862) (discrInv := 178800587211347090106220256638857830562910209432575336498897478520147655742906223746137194994125494770448172324763284421519535534377159647378281756093392340015717507915309519438801233411180020949823004575547017469129923616) (inverses := []) repair6Step28 (by decide +kernel)

private theorem repair6Step30 : Nat.Prime 251012880562072343257608454681181846413913202546655267750534063457514626232810662304951232553308650213240058550157233206127780208175494018923739158622458865488906085104374709201614118422772495998650220800820769600995607983898903 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 44454972493572324918078528363788677437642429338041506804172931137140372628345252649621652976719657679358950664708624143394501608576196957536635638674736498941909998273519097707109777716251463677556856329533546542476595674678195) (b := 87797587190615067497718674181353880940012032072318657078632695111297529175283343224524284503915173269088120772530674339935273979790921409527347121256167001015884876613987162210551085526660259837843352335853627741217507434126724) (x := 61205017327456608009645810327060819127014783995909715779929740971143985577642582014371062443243796597141536843062640642839915017365512544446591971224701278698607798270463734090291554307304035993185803123535141704290367507145479) (y := 101876661870223257866441297229596158119214141046678635034312927062217585341392586316032565915477170474261136157289338942201632700303248225365595027013058362682494594480025352479741243040168213081584549313806523599083234837408339) (discrInv := 42855172586565085771806371404432614367341719660637062612447185506689114518488526725962283248818126205197552517420329600774001326931293895015117477447973259541651348421360041183301656705021291176610244803155731556855893204349598) (inverses := []) repair6Step29 (by decide +kernel)

private theorem repair6Step31 : Nat.Prime 3348283153963853011151789104144751274499519047044861268843203669991435318121196144634689631688281329664278119365758299600719810380739457496512966371694159067794498722572864641142765212444928252051679742747593964649090003305225464431821 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 3348283153963853011151789104144751274499519047044861268843203669991435318121196144634689631688281329664278119365758299600719810380739457496512966371694159067794498722572864641142765212444928252051679742747593964649090003305222073337037) (b := 3348283153963853011151789104144751274499519047044861268843203669991435318121196144634689631688281329664278119365758299600719810380739457496512966371694159067794498722572864641142765212444928252051679742747593964649090003227239327319245) (x := 3262148455050443947954057324987314463293400861476599442195817192956474217890107836996023147862320313168606343692847161800573378764832426861106303061428228512624595984437367251690593440770113652237101032614316327617375203501766793885032) (y := 1500918596145866892905129351102560336698407975960319943154899348126668921848519633376839532054598669012623130142719065564319524833486428906568309512664531996177245111564272821920360361618990310782414378209014306116194632170878877465986) (discrInv := 1541271189350496536311480021360788052438230852573297923996297591823936958458364699845955771643445955283358324610694189125976042280381817621194322857581615107549508111708337166837562099009823253208546652633006309752291454313850154103896) (inverses := []) repair6Step30 (by decide +kernel)

private theorem repair6Step32 : Nat.Prime 246219350009885895028057963562388429721596632643490918265653825076490187553360279691856536755829455858192355785680402318763744522465868545110294581417756448048667937304031655256890700943868180527045373377697342088828736669043985283922843809 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 8191935312043282192723732007610242806334846692779969757187636520789383333483171381330873434638405828038854226592057583463445277812159597298790881199211254814452905036309081234503254113041076612104908704680204286763445928358150524052607675) (b := 90671720923753934438201920305165153611512684177571112425525273449208334865701610136953481077941541881555755287430077246073885401323349803149468894187078000185414352355845340010880115233033416296640586734530015303339935631928860202914198194) (x := 176959218920608827781096956507320820532254393626828289863652336190777544608165343008090465011678610475687565961989323431321462156716401771067931271388692093997925898298417914440098199653817960014312040420692294548885674277331530818340335680) (y := 33225625220666155555448037965652383911958994196504298661367390177257849429310808165229001231122378724598138983350899745381293079563505670553437022288172105768946003003403421728632047703513313990381467911687806757441058343418413442716409281) (discrInv := 178453032476112651304398596447994344550067713031332232967033750044411024142425172172916662501969151806728381583087634313185790651466181630981724761525986650226550091734471597393295877015687384331919962390117327602220738627837501932901802747) (inverses := []) repair6Step31 (by decide +kernel)

private theorem repair6Step33 : Nat.Prime 264932020610637223050190368793129950380437976724396228053843515782303441807415660948437633549272494503414974825392112895003075796571267174912872207270636256103058974081706309010824271964133766960546558815627308580282989614527285555476651856033 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 115088500269652302362090830483586185571929644640504497763910294833466008268904953401807549198793700704988007696624707689094995311074267575126896768368457283831768967302798039102263833872367907341474170823435116489349644188372789816901922416404) (b := 148976917187486629807577928942035140955298356519898351363568586583248882709625893030618409923978991455515091335872477826536700292606031430648909891217038220794424189621737355748370423394828969814245352373992609335964720967911539584517592579721) (x := 130440994352157042108831139535940124193913943507913397119139622804277371299340044182643185540212806157848385732408563066637793190458007418328383779249803485881816769418439408786345127317940178609479454382132093660355370208302993033819788282137) (y := 80845828900723726896181263662773609192280072462437637171874021632897799351628647302123680150646729301856986924607536693760671390217494425199487665634545977979686164048017911143398137813817265985331330301731170139486360548051649203893492926132) (discrInv := 260149292325707672860267188460358952941790791692642231908311063109676513124724919860109189142696967826902615397686844324390708906549762410258666644224184669308193557482847187702331357034628394430274984639952072022123595841954996448511627612138) (inverses := []) repair6Step32 (by decide +kernel)

private theorem repair6Step34 : Nat.Prime 8212892638929753914555901432587028461793577278456283069669148989251406696029885489401566640027447329605864219587155499744931479878097227334430940728483916385409610693725562547572565382588382245179211647202147109594843550805576818443607908502299 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 0) (b := 3768754002441766051818730530117792300435696716384153089234537576652580451974068847989947970552807656646002119631238938437432450291536597547914281957609732819341216917238185755556579609215834160403635118564091655164286576694097203486276255588041) (x := 1778686139562600760022880447046975506468811922421248744463582581792008474992193218838880856327512280446611843140590548735401119507432172022584799764812888177174345480675382047810301075885755678916120283104601349457298820965250195151876624857292) (y := 3402576643441814642347299591118824707954357325702010536125643352699339073937580811250786447750142675605397138751150184735560946582429505101207291794423930658885533037867408063929338102054800663673738499850934986280631578374825184201674581341253) (discrInv := 4151082716309961285153252383442103647905891505988071194641507755388280466389330114200718426461167633089223680537893648712674616120074041010939062167106712149834344782306366876813619677854207375401557748501875307865885991681613569671480645178349) (inverses := []) repair6Step33 (by decide +kernel)

private theorem repair6Step35 : Nat.Prime 32851570555719015658223605730348113847174309113825132278676595957005626784119541957606266560109789318423456878348621998979850418640453821294302474730710476540053016125989571870853345323266472615765601562038449016311096931615606629872516633425261 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 32851570555719015658223605730348113847174309113825132278676595957005626784119541957606266560109789318423456878348621998979850418640453821294302474730710476540053016125989571870853345323266472615765601562038448809533417823287577929678497420113261) (b := 32851570555719015658223605730348113847174309113825132278676595957005626784119541957606266560109789318423456878348621998979850418640453821294302474730710476540053016125989571870853345323266472579574350318729258682494233473521790851816047154001261) (x := 4438960901127874495258212241579110906722299103613662049524057829162835263209278221893877883512820940042391137179901078223657515696766771388839746467898824673463542905507839987254843579299355195007571359552945281478591931388933214789376184006900) (y := 27738963804870879175779727813415381710940698975471032866543225477143376715580365408926341887155186761556185720181717838383542400205777641655514344317287062984783731318292744726239352679194966429294703582234598917664315967539189065858946612792268) (discrInv := 15272799890980459111390534118764240106474114054629732491602986439869463565308913220779842190909524089090460519163593117108925243744294005417922235544803814553952838205278667524578874033150276426133865814505333369092377962196699049149611696880520) (inverses := []) repair6Step34 (by decide +kernel)

private theorem repair6Step36 : Nat.Prime 888439845203098402601938686787878211769812846132833706852466581657017591087335939874021329227602748914803073225472834257731013176188758786182323399779780708724323101760168986712634290872695933849497021096969733337199739759774908466778135721111377988007 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 224968763984593667308766971536795892248069443755148070834599805788285368408006997694846890901619017925741016731558527324436817828869029112674819564541348651087489268356722423329978860781003742636149607018458394277492824500670590264521830181190661283479) (b := 553589861533243179695046970115333869467994862347329588761745238236498590876475687439861824644659122922818851886177896082449006528297472668924022113145874668051032782801541177108055382720975076495845824656769844782577488036987307605825222168932081392418) (x := 106344392540107247821056979558183077769929149239990748332556359168723523585198709600133527289232794609200991076590942021734214270063525354361454104942018765233132651574112612350967887198095553393733914633689768326531671176462403023331749974735508029826) (y := 490685963810607291573546828796795162346087017955993862468218133037145252835158120419670339054869672516710785117264285625908939487921499935516811788470114571909790594247002807680890697511428130701248959978441392631379696991791076911779426096149227696191) (discrInv := 64979617758583353132950350915733620817896020866517354574967810747289752217903296624488398390598509375223376517917751567006671192245340956311546240530966088504304083628315520347327805427520701910893274571507662646763432057948847138507615616468475982062) (inverses := []) repair6Step35 (by decide +kernel)

private theorem repair6Step37 : Nat.Prime 90192105806740557385597258247935807939155433935443870950525711514107862572502290804574792509794226985491876250268835580894285130187583067723564078974677302693091104702284206568647243631851099480805412683121348167053036764567282498831434833667580881582241650303 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 90192105806740557385597258247935807939155433935443870950525711514107862572502290804574792509794226985491876250268835580894285130187583067723564078974677302693091104702284206568647243631851099480805412683121348167053036764567282498831434833665232603626682226303) (b := 90192105806740557385597258247935807939155433935443870950525711514107862572502290804574792509794226985491876250268835580894285130187583067723564078974677302693091104702284206568647243631851099480805412683121348167053036764567282498830049760265504795076409202303) (x := 34356840452125636924153321017067490580043466195811820348570681321737765364114607622096043464533326732987054368920013363897615404991603749485575717372383418256594880252696327772582631943361419901513438916747124232068538669961933122997203246602830662974929357563) (y := 78150993918764841263862397188777001424335965102490250462089736725266183980833425634854405590852003691056679176367305446477202126848398032785758987438704883717757021624980853252646648645325364751018016576887348015036116751911671339293385744489001013450291994431) (discrInv := 33578376035290289292399267759791621667243817430661027314408605838764489982528051841891596669538979628715558184731614408252158212476213279829829259648595418090951606924967066677539903977524853458823034273063958109253074903316712165275992991632460243337292569956) (inverses := []) repair6Step36 (by decide +kernel)

private theorem repair6Step38 : Nat.Prime 54851148180882100985052591212184311103269272618335757884354313181290956236967289046104956408522140582602139793329221049816769602926846165107093594671745437903045790167790872977376619519502082810594083309256069694107135420252484499089714121689032413668068014321069957739 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 21098674222386661886703052660439481633274609808432100356052844262444949815555647602156494046467897771484912644836674916623738810515226500768971458393984012549698149704594474341955838990005405787919663477404493983600747806550872847629583034994122279316296958822900950742) (b := 25946260750180657991865457010370371608571791685304754705625610728436519284929928924461579098873620833658815034654405225033846268691422453168044313333514041219998512192016821973548619203070884033456703863417311370541156018619071835325608201316992198245502875345684120403) (x := 5304937836558776465693296521547091885697287021364872336433767521658707946065731036658682756885850190264881659684631288283810156478974314224124981586579575733543276230747948751361219174689746524870762410844975267702492204235850195606454421009962295085023175745616620173) (y := 35220082768640391386210882982883859275777615588330886532063033224038033783469756183808785805500727002049882597946942667474961264164090540638135034895246231788023833230527284552975986233902183446058968075191732466239379190234623798425754277586091581888324993658240512265) (discrInv := 51033804021729237546431194028983995399246372132706728668056392400842335663467849891524192678728844481703840370328953254690629867187797912448011553737111313952988076788885034728837952253430616203716001431478403051580934863435874914203595217444318998504729235058325751373) (inverses := []) repair6Step37 (by decide +kernel)

private theorem repair6Step39 : Nat.Prime 2847708376534412378011399019225161971971897304988680382140212101936598925937580432621568128380197777158329274101628209144642423077623542600571570118866293270278164192834184769537429002651840505615431369086600305641031104030962517819689307556301195777747095397435985532038996353 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 2404129331724319970170239246268187432638548214840556580318382233883751189574374568149475904847146408086903625361065046434031484023634902735194699756233787422058795097821323517055393380475453537202202555567828256254031893169772274104872119722334215626920315681323267695347050389) (b := 1829381644027007977730349245651236570282431400070766212864393585784010318872338622594904740092533479897813910308065011314128759578124786778245041941902198201861394173776168345317189387788118148927552114153950055195548560762108306250608893125425208821565687993357321907473728252) (x := 1298348003570358585359640796409542012957078491803987621769965932502283597686638580629452350915979098537959534580283727379455553879955532779656055680287412536990178459350722175414171005878170150447172572762123698589163061756270914810187866212643701782010224510149921157125867275) (y := 2387576336919796677389421784131116169499133725644721211841920096837190087636049958341767364884038737553785007591634220972231758345118764688302548610678227494488224472777751626947729395499601930280607951345849692118874905479037637090933735083854159944203908481269595252478469941) (discrInv := 2648313633949741370333075606947572345450236388710367773274155153135996471743424701616812258696614495066402111401628303434632687255509444290908134211153667533839906369046657663722659035109603284572455052997431917113735406683142807651717439872977603938053459522256737493754942219) (inverses := []) repair6Step38 (by decide +kernel)

private theorem repair6Step40 : Nat.Prime 3138182718432711798299715271559343092573031230285871948970799014536501516324163299477396722728462550190165989715132735101509921016022684396690867967443549323248421963703699097107820569976464901625551261940791991422169265884096668718477129568612998735633476582501276125259054697907045037 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 175926725289712727788820581047380958339657789052501745879482382102736461930641614946383314405281186683947539621670401645068775365937255072922203208908163271302973190039417397636565530278216088007474534937571262234254198608208081773547441571916287038657969405983878640994907231529503280) (b := 1149690756217907573931818443874783461724110426527292338757252990084039509807273150310403405424179938648339727755410477888914348664778101551560538748034134981556982262360946272090553000052626577706650394920316109704898542276015012300128089034855336176587125505825327398827496826048401187) (x := 407118846115786437629087996549603881520647929429214823540187240371662971873242839686657823201960219405755968275468537219976697232192309873380536793995077151931492078155365874349745842018407140055326865538463414045005769080598979139918062820918526883143512161268321661708936173933827065) (y := 1041746018812715936807469137334583394022436676058189171036564411482314385282318831110065315847714444376609647061633612366807349580276742089694681517953937024281142300953483248212189250377612346714275651246844454162178376446910500177415700309594259630025011617768603931456900708384298469) (discrInv := 1146292988843502642335463771454017600612846998714489003872243794586822262747888580591772260722965883298144799902468934638188647319368795687607516874031624535836028708676099154716436216877947838377159326578346125322447038835376905850474784894760162421555175225947377351715566806695196635) (inverses := []) repair6Step39 (by decide +kernel)

private theorem repair6Step41 : Nat.Prime 7735620400936634582808798144393780723192521982654674354213019570832476237739062533211782921525660186218759164647802192025221955304495917037842988988972812898915828568242861428251367437468376503259091698740821362400374044592494886475916021077056590444704977898030994595485934202367590295789 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 3500210810537777387570635498411937108761616753446724154673771582641193105829447264570912304146193630520494470896427807112131405046826916084208299370025015120308169504401024066397920837219192198510917980595586058012709970011578539272164456629699944129571662655441409026401596657357857028226) (b := 120738762803219006147108362160370899222711185768055102497359136197256256594725320289792638542044611687659875503929684300620689770097663572649791197175728172126331681846546496116278088336153805656340252447053572193447011430153258053782956889829176501469373043227547910055285985073940643548) (x := 6384630010066170747693920007963734064378369902741347999134316336296405145972687370036363256469967284223184832053581124088117913804624340007868001087570601085024959638435624014209938818247026378996687825674986379507526045168243477371956134004629177112396066594504952456103400911650212999790) (y := 2344494965650741699843736380092878736125561631968427616067149640514347691653842531523289148443145893545887150305812165084879712163436212741671027561721079352676787086776027074086101997553623312802622250634888651768590604862561795844422235498912227439210531959077661756247788813545723893156) (discrInv := 7598741544046659030770929813171620251001685305796356792963895825216602121824904361112924132367087775519559037614966136747030834611060216118018011289697091016329203068441993574537076025653390814171830244942015009417576764398247077053657363173877211052118312853057387609534900866957120058061) (inverses := []) repair6Step40 (by decide +kernel)

private theorem repair6Step42 : Nat.Prime 2011261304243524991530287517542382988030055715490215332095385088416443821812156258635063559596671648416877382808428569926557708379168938429839177092357417573276973226033625056547280939925054340220309961568533302783518382167765334923166389153461071761193435849288602445488461513267866789820093 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 1) (b := 0) (x := 1673454927482618077306117659791752919829694887984716446908018142032806878890177989677975773564951359769388576292358891738080772893285108904793780454685538715402600872186929461035894699165631236676243530373078686034334947968237233057991544880904684555477126975492605668700836365795946197631921) (y := 48514570451057277040598686986632854686713685524987709963660262301336052895669125246864299320098369437195860798384486084093791017021951920063907101359476826974761422635063041549474011266540227419751421976425292289223598523109575111526038760533421874740860607826635882085558335737442272086288) (discrInv := 1508445978182643743647715638156787241022541786617661499071538816312332866359117193976297669697503736312658037106321427444918281284376703822379382819268063179957729919525218792410460704943790755165232471176399977087638786625824001192374791865095803820895076886966451834116346134950900092365070) (inverses := []) repair6Step41 (by decide +kernel)

private theorem repair6Step43 : Nat.Prime 90506758690958624618862938289407234461352507197059689944292328978739971981547031638577860181850224178759482226379285646695096877062602229342762969374592139309005645596025569536678022737162734923621171293219369991221898827136788585045054114043742579531624572168501105242558790741031031279310337 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 74235458760888353169927838068800510930177569580883583856691897874064180335766610158555618515649190418836671719671228574680020486169040850353253950835140678775075598596369214078419321896523748752767351811560636979565173126104762444867465431224108579583099479704429048319689578997930552026287524) (b := 60479324445708406014018542336284009585096789625714625628963199422854801842099821003466831229176060712854931329746054043746486508756863808151839033293275419849109440065280767138904246252627448795508257462387264740330471351156871164624047223077057321510603075483695107950848187697352489904134306) (x := 13126806552529579043012676400583958019717177100001086789516898255115865262353537815325395309063894765879231373434277032926995633293828533496280942676496727418542189396747574846449338538153908415717525151908440345911250283777397884943171803921010153584704834725871428286995997059087951790177215) (y := 88280947367844367211397450951741379974421732732517229235195094020456962266821989893949523031002128422000122532413756013566532458849980376381161866451129237690023325846356729459248462841751708272012819190323164126179466209219164311084799511395806573593968622982784621239500485839431159150943059) (discrInv := 77756435848661024080684075156196790214686357709498209451034074873203024347629888817864965179474056102933811627313556797674920078195338223913458242315226606874856818625786074385291286536487052751885097539172591164714925682974151186982971797581005086129178513672705640151374830236968097418895671) (inverses := []) repair6Step42 (by decide +kernel)

private theorem repair6Step44 : Nat.Prime 4120048669129818509899878676810396127149688832624551205644075399770201004543983974251341351198185905065489149909237841208854200037643778684141255891985905837058334953125188031696388047791799533515999090312568904007472953501822004907924560351785812116539799738626441532015508428925590036832400346743 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 794685986782408772506771276615707888479169108929323314260889954922121445547522264542174791934247357327129710060986475029294546076798631737294488520701433789250491645407282887172946525372990723480732420549374377042759425029860695655181956537069244078487163941281497931231106653688821067438711302054) (b := 3409822892150755771681964606678637395277996213830917624824532965481020953286102409454035581025308189451634371767155083644637865572123358263024422324254566592173123505091361238868678260705898406567537033810507597811166108208107347641427565092730773712935660649243701279477046399380724721779401816363) (x := 3756784762480927882902187600092758212008007574201194177504654666509136915942690186736428973050656358671335255292131058011049845519349605601432718050083216324785402057972232059313030738063770493785871174850475138638388819270992424725316684292864010863568173494999755678053629722585459325401869312399) (y := 2708278062021343998721596597681610119093543419721852332505226113745632147788611878072658572582678517903666394011862116177398213235893925466865918653869519188845294710969020308514483941344126480362226427618614121127136639933149478157144096310591644106506037481963905776879714782287145595051720493858) (discrInv := 500157677760244178533482072606456952193358393500849341830843932379302407255737050468293359269117913846320847789987936218642508316728391619227208701495768059917890022731730228543590634215572865501378005304164881550774114454705002806347583279249841724901993225625255483297495984240790872688122604981) (inverses := []) repair6Step43 (by decide +kernel)

private theorem repair6Step45 : Nat.Prime 336434934223802719881404292990983326950789290694455602350483908994435073629052643369416032056141464635837713003288543637432616266673915679789606673627812571065446630354567839822489281114335303068865810336045242311446227363298894271075443303981214835545526167575120781376941543733417500712684509997770531 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 155612601480348618850976273522905632253800402644808722191760306338619833963643973438512702246936503365093797663174205273381397618560521358424245881194067039368190687625171637299265320849618898498366447463766759066508135674518366824245716795049644694005250389086534043063181084925765807752071726824273861) (b := 36182471902000769857307358997731060563579636418096884702991157914566462328673875226572658073543072970888335959285193003663815493700262081601697295256848892751534682577357392167480123614499884841296314913487671329296958992184532693761897408503623226048446552416946358850333760986996148726883372014199661) (x := 196271305464304081023149755250716590893208111138689872023269323902852993347562763339282972963631797077896342363481960893302476137321753890763729966102856870544752232112009858245556791407654228010236418022452368357135325416036483957964362584684672107754260755928551760442455456182377515784337545091199322) (y := 71770622840405923704999909734949287735436212519834925155660916661656830041646130188060136115149042148449660087194846498218593856314962779902794771985071514639977399281356292790950358702845354555233437136510864910872274729141702493129572363918354093982139437696208646012458873257673727254528845146667586) (discrInv := 30585128347750938849060645599199338621367262292752807182357345859491269754264677632085236245714053343701658570068748932800097680459802567399269418122686567301361006367782189013384779339718059033765153781552660329167399589406599340527053659750063224269429347753592583833517224665223754267104215099810970) (inverses := []) repair6Step44 (by decide +kernel)

private theorem repair6Step46 : Nat.Prime 13793832303175911515137576012630316404982360918472679696369840268771838018791158378146057314301800050069346233134830289134737266933630542871373873618740548128495746789169325629071599484013587695161459135186644196381286230185438231139605919125563599157060051576559471949918944711452314010590906165425273641 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 13793832303175911515137576012630316404982360918472679696369840268771838018791158378146057314301800050069346233134830289134737266933630542871373873618740548128495746789169325629071599484013587695161459135186644196381286230185438231139605919125563599157060051576559471949712167032343985981890712146211961641) (b := 13793832303175911515137576012630316404982360918472679696369840268771838018791158378146057314301800050069346233134830289134737266933630542871373873618740548128495746789169325629071599484013587695161459135186644196381286230185438231139605919125563599157023860325316162759585127847994220194812849695945849641) (x := 11749511963829536854359310343002341926493316898002084226254731546798594716169491554691108576680306676595095260656602383687204663304731064321047373270384008888294458285349035937051010251595697387157840806795001702001966018882859457965919573256473411569028274070819485024524386250392899215229416636573363479) (y := 4003082063760851896257745628144541013915789305876850730777300740409050661454315495111799150900406783163459825764242397353510936109219663972414515910075535564966601097359370342936835380315915372838019798640952574254582572637957277502004989271508619151420181527545415851776582186217341161021100089581161752) (discrInv := 4600297018216126648701019079687039287299757875461251419094045576992261723135362782295660651555633920971198866351090688800806119909840314066178827400144998776760429533227948455965220732818561788806041142326929672563936494110675338648532754260113783580172825637932988988039033996339957303794732797438056342) (inverses := []) repair6Step45 (by decide +kernel)

private theorem repair6Step47 : Nat.Prime 9904900228486544729863776435014999898824078806686917627744333061873099520418829290629882504755268570197400187250230595284297401177418802048125460868235699513949236468913453862515987576770501101420692223961567307799428859399675949321439854231503287729310602820916129053062851468661711152190674846324182248615043276439 :=
  GoldbachRfc11PrimorialECPP.natPrime_of_step (a := 8295750286420616589877920101411923536822397201081183421139736427753271507046718250385889977036168819876008872538993074239315180546458994393462117776243773723462156483231550540408431060202962833881359422010697753021671896713797328938302063975943694335195489170868476650673929796625458552269044724333149902367992581275) (b := 7981458941837813225503665153484176318765760680328294786122861515177675388361245190087313902640829769003164390148805557289572422315327582070931605712287074901247972653154892789401142028950649616887634177852621481202628158907845112847783942021615749388794745422027916943398948899451914928615313370331262298459259094332) (x := 6069067448039717437498268272920321743140428558469592993919268964812360081550651413599798574801276378841435884121669852967270480618250613109754565509257657962249909917943886317711230035958370814968150106590743178298830533392542341790537389621530318813690667234935846257082648857347637935666847564590097673570758097771) (y := 2666625198278344677966111777685138533147723932429413192519666175133697842571851836689372712769898496471547463098170060281100359816602651255977614948727493201444682090094157977234763549524633582168320526110006162315108072926254190677901776641223429434022182028415445006932778542756279957830542151380897703696419523036) (discrInv := 9188180347672507248036447528124994144825677259864234166967816070034163365429707530352875872755918106184295226694111505194991575203602565273857878419431766900337437445012839335081479945359537496295224130343703493390958204992517013374637365582842928495350366783312491257916509421461134880760825042340439841988977201031) (inverses := []) repair6Step46 (by decide +kernel)

open Finset
private def W757 : ℕ := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p
private theorem W757_val : W757 = 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507212970 := by decide +kernel

theorem Conjectures.Goldbach.Rfc11Primorial757Repairs : let W := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p; 6*W < 10^316 ∧ (10:ℕ)^316 < 7*W ∧ (∀ k : ℕ, 1≤k → k≤6 → let n := k*W; (∀ p≤757, p.Prime → ¬ (n-p).Prime) ∧ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)) := by
  change 6*W757 < 10^316 ∧ (10:ℕ)^316 < 7*W757 ∧ _
  refine ⟨by rw [W757_val]; decide, by rw [W757_val]; decide, ?_⟩
  intro k hk hk6
  change (∀ p ≤ 757, p.Prime → ¬ (k*W757-p).Prime) ∧ _
  constructor
  · intro p hp hprime hbad
    have hmem : p ∈ (Finset.range 758).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hprime⟩
    have hd : p ∣ W757 := Finset.dvd_prod_of_mem _ hmem
    have hd' : p ∣ k * W757 := dvd_mul_of_dvd_right hd k
    have hsub : p ∣ k*W757-p := Nat.dvd_sub hd' (dvd_refl p)
    have hW : 1515 ≤ W757 := by rw [W757_val]; decide
    have hn : W757 ≤ k*W757 := by nlinarith
    have heq := (Nat.prime_dvd_prime_iff_eq hprime hbad).mp hsub
    omega
  · interval_cases k
    · refine ⟨1097, 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507211873, by decide +kernel, repair1Step47, ?_⟩
      rw [W757_val]
      decide
    · refine ⟨1097, 3301633409495514909954592145004999966274692935562305875914777687291033173472943096876627501585089523399133395750076865094765800392472934016041820289411899837983078822971151287505329192256833700473564074653855769266476286466558649773813284743834429243103534273638709684354283822887237050730224948774727416205014424843, by decide +kernel, repair2Step41, ?_⟩
      rw [W757_val]
      decide
    · refine ⟨1013, 4952450114243272364931888217507499949412039403343458813872166530936549760209414645314941252377634285098700093625115297642148700588709401024062730434117849756974618234456726931257993788385250550710346111980783653899714429699837974660719927115751643864655301410458064526531425734330855576095337423162091124307521637897, by decide +kernel, repair3Step45, ?_⟩
      rw [W757_val]
      decide
    · refine ⟨1109, 6603266818991029819909184290009999932549385871124611751829555374582066346945886193753255003170179046798266791500153730189531600784945868032083640578823799675966157645942302575010658384513667400947128149307711538532952572933117299547626569487668858486207068547277419368708567645774474101460449897549454832410028850771, by decide +kernel, repair4Step41, ?_⟩
      rw [W757_val]
      decide
    · refine ⟨811, 8254083523738787274886480362512499915686732338905764689786944218227582933682357742191568753962723808497833489375192162736914500981182335040104550723529749594957697057427878218763322980642084251183910186634639423166190716166396624434533211859586073107758835684096774210885709557218092626825562371936818540512536064039, by decide +kernel, repair5Step44, ?_⟩
      rw [W757_val]
      decide
    · refine ⟨1381, 9904900228486544729863776435014999898824078806686917627744333061873099520418829290629882504755268570197400187250230595284297401177418802048125460868235699513949236468913453862515987576770501101420692223961567307799428859399675949321439854231503287729310602820916129053062851468661711152190674846324182248615043276439, by decide +kernel, repair6Step47, ?_⟩
      rw [W757_val]
      decide

#print axioms Conjectures.Goldbach.Rfc11Primorial757Repairs
