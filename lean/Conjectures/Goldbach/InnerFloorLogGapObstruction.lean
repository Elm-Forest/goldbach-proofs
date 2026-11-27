import Conjectures.Goldbach.InnerFloorQuadraticPacket

/-!
A precise model obstruction to discarding the odd quadratic packet
using only the logarithmic zero-free bound. This does NOT assert that
such zeros exist, or that the frozen integral theorem is false.
-/
open Finset
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem logarithmicGapAmplitude (q c k : ℝ) (hq : 1 < q) :
    (q^k) ^ (-(c/Real.log q)) = Real.exp (-k*c) := by
  have hqp : 0 < q := by linarith
  have hL : Real.log q ≠ 0 := (Real.log_pos hq).ne'
  rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos hqp k),Real.log_rpow hqp]
  congr 1
  field_simp
  <;> ring

theorem logarithmicGapSquaredAmplitude (q c k : ℝ) (hq : 1 < q) :
    ((q^k) ^ (-(c/Real.log q)))^2 = Real.exp (-2*k*c) := by
  rw [logarithmicGapAmplitude q c k hq,pow_two,← Real.exp_add]
  congr 1
  ring

/-- The real model amplitude allowed by a c/log q gap has a negative
signed quadratic packet uniformly bounded away from zero at q|n.
The zero-frequency shift here is only the algebraic packet; no
identification with an actual zero or full arc integral is asserted. -/
theorem oddQuadratic_logGapModel
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hquad : χ.IsQuadratic) (horder : χ*χ=1)
    (hodd : χ (-1) = -1) (hq : 1 < q) (c k : ℝ) :
    let z : ℝ := ((q:ℝ)^k)^(-(c/Real.log q))
    (signedCharacterPacket (0:ZMod q) {χ}
      (fun ψ => gaussSum ψ⁻¹ ZMod.stdAddChar*(z:ℂ)/(q.totient:ℂ))).re
      ≤ -Real.exp (-2*k*c) := by
  dsimp only
  rw [oddPrimitiveQuadraticPacket_negative χ hp hquad horder hodd]
  rw [logarithmicGapSquaredAmplitude (q:ℝ) c k (by exact_mod_cast hq)]
  have hφ : 0 < (q.totient:ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hr : 1 ≤ (q:ℝ)/(q.totient:ℝ) :=
    (le_div_iff₀ hφ).2 (by simpa only [one_mul] using
      (show (q.totient:ℝ) ≤ (q:ℝ) by exact_mod_cast Nat.totient_le q))
  have he := Real.exp_pos (-2*k*c)
  have hm := mul_le_mul_of_nonneg_right hr he.le
  linarith only [hm]

end
end InnerFloorResearch
