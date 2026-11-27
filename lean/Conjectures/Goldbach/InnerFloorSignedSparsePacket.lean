import Conjectures.Goldbach.InnerFloorReducedGaussEnergy

/-!
Signed sparse character packets: exact Gauss expansion, conductor-sensitive
bounds, and the genuine divisibility obstruction. These are algebraic
lemmas, not assertions about the distribution of Dirichlet L-zeros.
-/

open Finset
open scoped Classical
open DyadicMixedB4CharacterFactorBound
open Conjectures.Goldbach.ReflectionCharacterContraction_aux
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1200000

variable {q : ℕ} [NeZero q]

def signedCharacterPacket (n : ZMod q)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ,
    (∑ χ ∈ S, w χ * χ (a : ZMod q))^2 *
      ZMod.stdAddChar (-n * (a : ZMod q))

/-- The signed quadratic expression uses the PRODUCT character, not the
conjugate-product appearing in ordinary Parseval. -/
theorem signedCharacterPacket_eq (n : ZMod q)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) :
    signedCharacterPacket n S w =
      ∑ χ ∈ S, ∑ ψ ∈ S,
        (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-n)) := by
  unfold signedCharacterPacket
  have he (a : (ZMod q)ˣ) :
      (∑ χ∈S,w χ*χ (a:ZMod q))^2 * ZMod.stdAddChar (-n*(a:ZMod q)) =
        ∑ χ∈S, ∑ ψ∈S,
          (w χ*w ψ)*((χ*ψ) (a:ZMod q) * ZMod.stdAddChar (-n*(a:ZMod q))) := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,MulChar.mul_apply]
    apply sum_congr rfl
    intro χ _
    apply sum_congr rfl
    intro ψ _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro χ _
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro ψ _
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_units_eq_sum (fun a : ZMod q =>
    (χ*ψ) a * ZMod.stdAddChar (-n*a))
    (fun a ha => by rw [MulChar.map_nonunit _ ha,zero_mul])]
  unfold gaussSum
  simp only [AddChar.mulShift_apply]

/-- An unconditional divisor-sensitive bound for arbitrary n>0. -/
theorem signedCharacterPacket_divisorBound (n : ℕ) (hn : 0<n)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) :
    ‖signedCharacterPacket (n:ZMod q) S w‖ ≤
      ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*
        (Real.sqrt (χ*ψ).conductor *
          ∑ f∈n.divisors.filter (fun f => (χ*ψ).conductor*f ∣ q), (f:ℝ)) := by
  rw [signedCharacterPacket_eq]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro χ _
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro ψ _
  simp only [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_gauss_neg_shift_le (χ*ψ) (n:ZMod q)).trans
    (by simpa only [DirichletCharacter.changeLevel_self] using
      norm_dirichlet_gauss_induced (dvd_refl q) (χ*ψ) n hn)

/-- When n is a unit modulo q, every packet entry enjoys square-root
Gauss cancellation, including all imprimitive characters. -/
theorem norm_gauss_unit_shift (n : ℕ) (hnq : n.Coprime q)
    (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt q := by
  let u := ZMod.unitOfCoprime n hnq
  have hu : (u:ZMod q) = (n:ZMod q) := ZMod.coe_unitOfCoprime n hnq
  apply (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
  rw [← hu,gaussSum_mulShift_eq χ ZMod.stdAddChar u,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans
  exact (norm_dirichlet_gauss_standard χ).trans
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level))

theorem signedCharacterPacket_unitBound (n : ℕ) (hnq : n.Coprime q)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) :
    ‖signedCharacterPacket (n:ZMod q) S w‖ ≤
      Real.sqrt q*(∑ χ∈S,‖w χ‖)^2 := by
  rw [signedCharacterPacket_eq]
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*Real.sqrt q := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro χ _
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro ψ _
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_gauss_unit_shift n hnq (χ*ψ)) (by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

/-- The unit-shift estimate for the actual Gauss-normalized Fourier
synthesis. At modulus q this saves q^{-1/2} up to totient losses, compared
to the worst-case unnormalized quadratic energy. -/
theorem normalizedSignedPacket_unitBound (n : ℕ) (hnq : n.Coprime q)
    (S : Finset (DirichletCharacter ℂ q))
    (F : DirichletCharacter ℂ q → ℂ) :
    ‖signedCharacterPacket (n:ZMod q) S
      (fun χ => gaussSum χ⁻¹ ZMod.stdAddChar*F χ/(q.totient:ℂ))‖ ≤
      Real.sqrt q*(Real.sqrt q/(q.totient:ℝ))^2*(∑ χ∈S,‖F χ‖)^2 := by
  let w (χ : DirichletCharacter ℂ q) :=
    gaussSum χ⁻¹ ZMod.stdAddChar*F χ/(q.totient:ℂ)
  have hw (χ : DirichletCharacter ℂ q) :
      ‖w χ‖ ≤ (Real.sqrt q/(q.totient:ℝ))*‖F χ‖ := by
    unfold w
    rw [norm_div,norm_mul,Complex.norm_natCast]
    have hg := norm_dirichlet_gauss_standard χ⁻¹
    rw [DirichletCharacter.conductor_inv] at hg
    have hd : (χ.conductor:ℝ)≤q := by
      exact_mod_cast (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
    have hq := Real.sqrt_le_sqrt hd
    calc
      _ ≤ (Real.sqrt q*‖F χ‖)/(q.totient:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hg.trans hq)
          (norm_nonneg _)) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hs : (∑ χ∈S,‖w χ‖) ≤ (Real.sqrt q/(q.totient:ℝ))*(∑ χ∈S,‖F χ‖) := by
    rw [mul_sum]
    exact sum_le_sum fun χ _ => hw χ
  calc
    _ ≤ Real.sqrt q*(∑ χ∈S,‖w χ‖)^2 := signedCharacterPacket_unitBound n hnq S w
    _ ≤ Real.sqrt q*((Real.sqrt q/(q.totient:ℝ))*(∑ χ∈S,‖F χ‖))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _ => norm_nonneg _) hs 2)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- A one-character packet already has a negative real signed energy
when the shift vanishes modulo q. This rules out relying on generic
sparsity or positivity of the signed quadratic form alone. -/
theorem signedCharacterPacket_negativeDirection
    (χ : DirichletCharacter ℂ q) (hχ : χ*χ=1) (c : ℝ) :
    (signedCharacterPacket (0:ZMod q) {χ} (fun _ => (c:ℂ)*Complex.I)).re =
      -(q.totient:ℝ)*c^2 := by
  rw [signedCharacterPacket_eq]
  simp only [sum_singleton,hχ,neg_zero]
  have hg : gaussSum (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (0:ZMod q)) =
      ((q.totient:ℝ):ℂ) := by
    unfold gaussSum
    simp only [AddChar.mulShift_apply,zero_mul,AddChar.map_zero_eq_one,mul_one]
    rw [MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient,totient_cast]
  rw [hg]
  simp [Complex.mul_re,Complex.mul_im]
  ring

end
end InnerFloorResearch
