import Conjectures.Goldbach.InnerFloorSignedSparsePacket

/-!
Exact sign of the actual Gauss-normalized single primitive quadratic
character packet, not an arbitrary imaginary coefficient.
The primitive Gauss product and square proofs are adapted from
PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero, lines 2155--2190
(source: OAI.NumberTheory.SiegelZeros.Characters.IntegerCharacter),
pinned upstream 1fe24b28926cd452b7a35f71ae1fc1cb82e01e84.
These finite algebraic results do not assert that a near-one zero exists.
-/

open Finset AddChar MulChar
open scoped Classical
namespace InnerFloorResearch
noncomputable section

theorem inner_primitive_gaussSum_mul_inv {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = q := by
  classical
  calc
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ =
        ∑ a : ZMod q, gaussSum χ (e.mulShift a) * e (-a) := by
      simp_rw [gaussSum_mulShift_of_isPrimitive e hχ]
      change gaussSum χ e * (∑ a : ZMod q, χ⁻¹ a * e (-a)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ZMod q, χ b * ∑ a : ZMod q, e (a * (b - 1)) := by
      simp only [gaussSum, mulShift_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext b
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = q := by
      simp_rw [sum_mulShift _ he]
      simp [sub_eq_zero]

theorem inner_primitive_quadratic_gaussSum_sq {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e ^ 2 = χ (-1) * q := by
  rw [pow_two, ← inner_primitive_gaussSum_mul_inv hχ he, hquad.inv, mul_rotate']
  congr 1
  rw [mul_comm, ← gaussSum_mulShift χ e (-1 : (ZMod q)ˣ), e.inv_mulShift]
  rfl


variable {q : ℕ} [NeZero q]

theorem primitiveQuadraticPacket_at_zero
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hquad : χ.IsQuadratic) (horder : χ*χ=1) (z : ℂ) :
    signedCharacterPacket (0:ZMod q) {χ}
      (fun ψ => gaussSum ψ⁻¹ ZMod.stdAddChar*z/(q.totient:ℂ)) =
        χ (-1)*(q:ℂ)/(q.totient:ℂ)*z^2 := by
  rw [signedCharacterPacket_eq]
  simp only [sum_singleton,horder,neg_zero,hquad.inv]
  have hg : gaussSum (1:DirichletCharacter ℂ q)
      (ZMod.stdAddChar.mulShift (0:ZMod q)) = (q.totient:ℂ) := by
    unfold gaussSum
    simp only [AddChar.mulShift_apply,zero_mul,AddChar.map_zero_eq_one,mul_one]
    rw [MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient,totient_cast]
  have hs := inner_primitive_quadratic_gaussSum_sq hp hquad
    (ZMod.isPrimitive_stdAddChar q)
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast
    (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [hg]
  calc
    _ = (gaussSum χ ZMod.stdAddChar)^2*z^2/(q.totient:ℂ) := by
      field_simp
      ring
    _ = _ := by rw [hs]; ring

/-- At a shift divisible by its conductor, an ODD primitive quadratic
character with real transform amplitude has a negative signed contribution,
with the exact factor q/phi(q), rather than a saving q^{-1/2}. -/
theorem oddPrimitiveQuadraticPacket_negative
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hquad : χ.IsQuadratic) (horder : χ*χ=1)
    (hodd : χ (-1) = -1) (z : ℝ) :
    (signedCharacterPacket (0:ZMod q) {χ}
      (fun ψ => gaussSum ψ⁻¹ ZMod.stdAddChar*(z:ℂ)/(q.totient:ℂ))).re =
      -((q:ℝ)/(q.totient:ℝ))*z^2 := by
  rw [primitiveQuadraticPacket_at_zero χ hp hquad horder,hodd]
  norm_cast

end
end InnerFloorResearch
