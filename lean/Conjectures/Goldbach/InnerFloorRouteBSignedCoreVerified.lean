import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Route B Signed Spectral Core (Standalone Verified Module):
1. Exact finite-sum signed bilinear decomposition (S^2 - M^2) under S = M + g + b,
   preserving all sign cancellation in the bad quadratic and model-bad cross terms
   while absorbing all good-spectrum L2 energy via Cauchy--Schwarz.
2. Exact vanishing of the model-bad cross Gauss sum at q ∣ n for any nonprincipal χ
   and any additive character e.
3. Exact Gauss-sum square identity `gaussSum χ e ^ 2 = χ (-1) * q` for any primitive
   quadratic character and any primitive additive character e, plus exact 3-way parity
   & reality partition of any triple-gate residual Finset.
-/
namespace InnerFloorRouteB
open Finset AddChar MulChar
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Pointwise complex identity for S = M + g + b. -/
theorem sq_sub_sq_split (M g b : ℂ) :
    (M + g + b) ^ 2 - M ^ 2 =
      b ^ 2 + 2 * M * b + (g ^ 2 + 2 * M * g + 2 * b * g) := by
  ring

/-- Finite-sum Cauchy--Schwarz in norm form. -/
theorem sum_norm_mul_le_sqrt {ι : Type*} (s : Finset ι) (u v : ι → ℂ) :
    ∑ i ∈ s, ‖u i‖ * ‖v i‖ ≤
      Real.sqrt (∑ i ∈ s, ‖u i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := by
  have h1 : 0 ≤ ∑ i ∈ s, ‖u i‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖u i‖) (fun i => ‖v i‖)
  have hnn : 0 ≤ ∑ i ∈ s, ‖u i‖ * ‖v i‖ := sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : (∑ i ∈ s, ‖u i‖ * ‖v i‖) ^ 2 ≤
      (Real.sqrt (∑ i ∈ s, ‖u i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]
    exact hcs
  exact (sq_le_sq₀ hnn (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsq

/-- Exact signed bilinear lower bound on any finite cell sum weighted by a
    unit-modulus phase e(i).  Only the controlled error g enters through its
    L2 energy; the bad quadratic and model-bad cross terms retain full sign. -/
theorem signedBilinearCellFloor {ι : Type*} (s : Finset ι)
    (M g b e : ι → ℂ) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    (∑ i ∈ s, (b i ^ 2 * e i).re) + 2 * (∑ i ∈ s, (M i * b i * e i).re) -
      ((∑ i ∈ s, ‖g i‖ ^ 2) +
        2 * Real.sqrt (∑ i ∈ s, ‖g i‖ ^ 2) *
          (Real.sqrt (∑ i ∈ s, ‖M i‖ ^ 2) + Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2))) ≤
      ∑ i ∈ s, (((M i + g i + b i) ^ 2 - M i ^ 2) * e i).re := by
  have hsplit :
      (∑ i ∈ s, (((M i + g i + b i) ^ 2 - M i ^ 2) * e i).re) =
        (∑ i ∈ s, (b i ^ 2 * e i).re) + 2 * (∑ i ∈ s, (M i * b i * e i).re) +
          (∑ i ∈ s, ((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have h1 := sq_sub_sq_split (M i) (g i) (b i)
    rw [h1, add_mul, add_mul, Complex.add_re, Complex.add_re]
    have h2 : (2 * M i * b i * e i).re = 2 * (M i * b i * e i).re := by
      have hm : (2 : ℂ) * M i * b i * e i = ((2 : ℝ) : ℂ) * (M i * b i * e i) := by
        push_cast; ring
      rw [hm, Complex.re_ofReal_mul]
    rw [h2]
  rw [hsplit]
  suffices herr :
      -(∑ i ∈ s, ((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) ≤
        (∑ i ∈ s, ‖g i‖ ^ 2) +
          2 * Real.sqrt (∑ i ∈ s, ‖g i‖ ^ 2) *
            (Real.sqrt (∑ i ∈ s, ‖M i‖ ^ 2) + Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2)) by
    linarith
  have hterm : ∀ i ∈ s,
      -(((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) ≤
        ‖g i‖ ^ 2 + 2 * (‖g i‖ * ‖M i‖) + 2 * (‖g i‖ * ‖b i‖) := by
    intro i hi
    have hre : -(((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) ≤
        ‖(g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i‖ := by
      have habs := Complex.abs_re_le_norm ((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i)
      exact (neg_le_abs _).trans habs
    have hmul : ‖(g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i‖ ≤
        ‖g i ^ 2 + 2 * M i * g i + 2 * b i * g i‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (he i hi)
    have htri : ‖g i ^ 2 + 2 * M i * g i + 2 * b i * g i‖ ≤
        ‖g i‖ ^ 2 + 2 * (‖g i‖ * ‖M i‖) + 2 * (‖g i‖ * ‖b i‖) := by
      calc
        ‖g i ^ 2 + 2 * M i * g i + 2 * b i * g i‖
            ≤ ‖g i ^ 2 + 2 * M i * g i‖ + ‖2 * b i * g i‖ := norm_add_le _ _
        _ ≤ (‖g i ^ 2‖ + ‖2 * M i * g i‖) + ‖2 * b i * g i‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ = ‖g i‖ ^ 2 + 2 * (‖g i‖ * ‖M i‖) + 2 * (‖g i‖ * ‖b i‖) := by
            simp only [norm_pow, norm_mul, Complex.norm_ofNat]
            ring
    exact hre.trans (hmul.trans htri)
  have hsum :
      -(∑ i ∈ s, ((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) ≤
        (∑ i ∈ s, ‖g i‖ ^ 2) + 2 * (∑ i ∈ s, ‖g i‖ * ‖M i‖) + 2 * (∑ i ∈ s, ‖g i‖ * ‖b i‖) := by
    rw [← sum_neg_distrib]
    calc
      ∑ i ∈ s, -(((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re)
          ≤ ∑ i ∈ s, (‖g i‖ ^ 2 + 2 * (‖g i‖ * ‖M i‖) + 2 * (‖g i‖ * ‖b i‖)) :=
          sum_le_sum hterm
      _ = (∑ i ∈ s, ‖g i‖ ^ 2) + 2 * (∑ i ∈ s, ‖g i‖ * ‖M i‖) + 2 * (∑ i ∈ s, ‖g i‖ * ‖b i‖) := by
          simp only [sum_add_distrib, ← mul_sum]
  have hcsM := sum_norm_mul_le_sqrt s g M
  have hcsB := sum_norm_mul_le_sqrt s g b
  nlinarith only [hsum, hcsM, hcsB]

/-- Exact vanishing of the shifted Gauss sum `gaussSum ψ (e.mulShift (-n))`
    when `q ∣ n` and `ψ ≠ 1`. -/
theorem shiftedGauss_nonprincipal_eq_zero_of_dvd {q : ℕ} [NeZero q]
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (e : AddChar (ZMod q) ℂ)
    {n : ℕ} (hdvd : q ∣ n) :
    gaussSum ψ (e.mulShift (-(n : ZMod q))) = 0 := by
  have hzero : (-(n : ZMod q)) = 0 := by
    have hq : (n : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff n q).2 hdvd
    simp [hq]
  rw [hzero]
  unfold gaussSum
  simp only [AddChar.mulShift_apply, zero_mul, AddChar.map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one hψ

/-- Primitive Gauss-sum product identity for any primitive additive character e. -/
theorem primitive_gaussSum_mul_inv {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) ℂ} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = q := by
  classical
  calc
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹
        = ∑ a : ZMod q, gaussSum χ (e.mulShift a) * e (-a) := by
      simp_rw [gaussSum_mulShift_of_isPrimitive e hχ]
      change gaussSum χ e * (∑ a : ZMod q, χ⁻¹ a * e (-a)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ZMod q, χ b * ∑ a : ZMod q, e (a * (b - 1)) := by
      simp only [gaussSum, AddChar.mulShift_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext b
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = q := by
      simp_rw [AddChar.sum_mulShift _ he]
      simp [sub_eq_zero]

/-- Exact Gauss-sum square for any primitive quadratic character:
    `+q` when even (`χ (-1) = 1`), `-q` when odd (`χ (-1) = -1`). -/
theorem primitive_quadratic_gaussSum_sq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) ℂ} (he : e.IsPrimitive) :
    gaussSum χ e ^ 2 = χ (-1) * (q : ℂ) := by
  rw [pow_two, ← primitive_gaussSum_mul_inv hχ he, hquad.inv, mul_rotate']
  congr 1
  rw [mul_comm, ← gaussSum_mulShift χ e (-1 : (ZMod q)ˣ), AddChar.inv_mulShift]
  rfl

/-- For every Dirichlet character, `χ (-1) ≠ 1` implies `χ (-1) = -1`. -/
theorem neg_one_eq_neg_one_of_ne_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ (-1) ≠ 1) :
    χ (-1) = -1 := by
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]
    simp
  have hfac : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by
    calc
      (χ (-1) - 1) * (χ (-1) + 1) = χ (-1) * χ (-1) - 1 := by ring
      _ = 1 - 1 := by rw [hsq]
      _ = 0 := sub_self 1
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact eq_neg_of_add_eq_zero_left h2

/-- Exact 3-way parity & reality partition of any pair Finset. -/
theorem pair_parity_split {α : Type*} (R3 : Finset (α × α))
    (isQuad : α → Prop) (isEven : α → Prop) (f : α × α → ℝ) :
    (∑ ij ∈ R3, f ij) =
      (∑ ij ∈ R3.filter (fun ij => ij.1 = ij.2 ∧ isQuad ij.1 ∧ isEven ij.1), f ij) +
      (∑ ij ∈ R3.filter (fun ij => ij.1 = ij.2 ∧ isQuad ij.1 ∧ ¬isEven ij.1), f ij) +
      (∑ ij ∈ R3.filter (fun ij => ¬(ij.1 = ij.2 ∧ isQuad ij.1)), f ij) := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨x, y⟩ _
  by_cases h1 : x = y
  · subst h1
    by_cases h2 : isQuad x <;> by_cases h3 : isEven x <;> simp [h2, h3]
  · simp [h1]

end
end InnerFloorRouteB

#print axioms InnerFloorRouteB.signedBilinearCellFloor
#print axioms InnerFloorRouteB.shiftedGauss_nonprincipal_eq_zero_of_dvd
#print axioms InnerFloorRouteB.primitive_quadratic_gaussSum_sq
#print axioms InnerFloorRouteB.neg_one_eq_neg_one_of_ne_one
#print axioms InnerFloorRouteB.pair_parity_split
