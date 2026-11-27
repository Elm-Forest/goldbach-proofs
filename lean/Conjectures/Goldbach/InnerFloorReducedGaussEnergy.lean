import Mathlib
import Conjectures.Goldbach.ReflectionCharacterContraction
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4

/-!
Research-only reduced-numerator projection for the inner-remainder problem.
Unlike the full additive Parseval bound (which pays q for every character),
this theorem pays the conductor of each character. It is an exact finite
identity followed by the already verified conductor-sensitive Gauss bound.
No prime distribution assumption is included.
-/

open Finset
open scoped Classical
namespace InnerFloorResearch
noncomputable section

variable {q : ℕ} [NeZero q]

open DyadicMixedB4RamanujanCharacters
open DyadicMixedB4CharacterFactorBound
open Conjectures.Goldbach.ReflectionCharacterContraction_aux

def unitAdditiveError (b : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) : ℂ :=
  ∑ r : (ZMod q)ˣ, b r * ZMod.stdAddChar ((a : ZMod q) * (r : ZMod q))

def unitCharacterError (b : (ZMod q)ˣ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ r : (ZMod q)ˣ, b r * χ (r : ZMod q)

theorem reducedSynthesis (b : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    unitAdditiveError b a =
      ∑ χ : DirichletCharacter ℂ q,
        (gaussSum χ⁻¹ ZMod.stdAddChar * unitCharacterError b χ /
          (q.totient : ℂ)) * χ (a : ZMod q) := by
  have hExp (r : (ZMod q)ˣ) :
      ZMod.stdAddChar ((a : ZMod q) * (r : ZMod q)) =
        (∑ χ : DirichletCharacter ℂ q,
          (χ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) *
            χ (a : ZMod q)) / (q.totient : ℂ) := by
    have hFintype :
        DyadicMixedB4RamanujanCharacters.unitFintype q =
          (inferInstance : Fintype (ZMod q)ˣ) := Subsingleton.elim _ _
    have h := unit_character_expansion
      (fun x : (ZMod q)ˣ => ZMod.stdAddChar ((x : ZMod q) * (r : ZMod q))) a
    rw [hFintype] at h
    have ht (χ : DirichletCharacter ℂ q) :
        (∑ x : (ZMod q)ˣ, star (χ (x : ZMod q)) *
          ZMod.stdAddChar ((x : ZMod q) * (r : ZMod q))) =
          χ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
      have h' := unit_twisted_gauss χ (1 : (ZMod q)ˣ) r
      rw [hFintype] at h'
      simpa only [Units.val_one, one_mul, map_one] using h' 
    simpa only [ht] using h
  unfold unitAdditiveError
  simp_rw [hExp, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  unfold unitCharacterError
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem reducedGaussEnergy (b : (ZMod q)ˣ → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖unitAdditiveError b a‖^2) =
      (∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖^2 * ‖unitCharacterError b χ‖^2) /
        (q.totient : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  simp_rw [reducedSynthesis]
  rw [synth_norm]
  simp only [norm_div, norm_mul, Complex.norm_natCast, Nat.cast_ofNat, mul_pow]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro χ _
  field_simp

theorem reducedConductorEnergy (b : (ZMod q)ˣ → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖unitAdditiveError b a‖^2) ≤
      (∑ χ : DirichletCharacter ℂ q,
        (χ.conductor : ℝ) * ‖unitCharacterError b χ‖^2) /
        (q.totient : ℝ) := by
  rw [reducedGaussEnergy]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro χ _
  have hg := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at hg
  have hs := pow_le_pow_left₀ (norm_nonneg _) hg 2
  rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hs
  exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)

end
end InnerFloorResearch
