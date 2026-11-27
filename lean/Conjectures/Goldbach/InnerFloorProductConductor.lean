import Conjectures.Goldbach.InnerFloorSignedSparsePacket
import Conjectures.Goldbach.InnerFloorArithmeticCore

/-!
A product-conductor saving for arbitrary shifts, including noncoprime
shifts. The low-product-conductor packet is kept separate.
-/
open Finset
open scoped Classical
open DyadicMixedB4CharacterFactorBound
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem divisorSum_le_log (m : ℕ) (hm : 0<m) :
    (∑ f ∈ m.divisors, (f:ℝ)) ≤ (m:ℝ)*(1+Real.log m) := by
  have hsub : m.divisors ⊆ Icc 1 m := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)⟩
  have hh : (∑ i∈Icc 1 m,(i:ℝ)⁻¹) ≤ 1+Real.log m := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using harmonic_le_one_add_log m
  calc
    _ = ∑ ab∈m.divisorsAntidiagonal,(ab.1:ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => (a:ℝ))]
    _ = ∑ ab∈m.divisorsAntidiagonal,(m:ℝ)*(ab.2:ℝ)⁻¹ := by
      apply sum_congr rfl
      intro ab hab
      have hp := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have hb : ab.2 ≠ 0 := by
        intro hb
        rw [hb,mul_zero] at hp
        omega
      have he : (ab.1:ℝ)*(ab.2:ℝ)=(m:ℝ) := by exact_mod_cast hp
      rw [← he]
      field_simp
    _ = (m:ℝ)*(∑ f∈m.divisors,(f:ℝ)⁻¹) := by
      rw [← mul_sum,Nat.sum_divisorsAntidiagonal' (fun _ b => (b:ℝ)⁻¹)]
    _ ≤ (m:ℝ)*(∑ f∈Icc 1 m,(f:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

variable {q : ℕ} [NeZero q]

/-- Even when the shift is not invertible modulo q, the shifted Gauss sum
is at most q (1+log q) / sqrt(conductor). -/
theorem shiftedGauss_productConductor (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : 0<n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt χ.conductor := by
  let d := χ.conductor
  have hd : d∣q := χ.conductor_dvd_level
  have hdp : 0<d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0<m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hdR : 0<(d:ℝ) := by exact_mod_cast hdp
  have hmR : 0<(m:ℝ) := by exact_mod_cast hmp
  have hqR : (q:ℝ)=(d:ℝ)*(m:ℝ) := by exact_mod_cast hm
  have hsub : n.divisors.filter (fun f => d*f∣q) ⊆ m.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left hdp hdiv,hmp.ne'⟩
  have hmq : m≤q := by
    rw [hm]
    exact Nat.le_mul_of_pos_left _ hdp
  have hlog : Real.log m≤Real.log q :=
    Real.log_le_log hmR (by exact_mod_cast hmq)
  have hs : (Real.sqrt (d:ℝ))^2=(d:ℝ) := Real.sq_sqrt hdR.le
  have hroot : 0<Real.sqrt (d:ℝ) := Real.sqrt_pos.2 hdR
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f∣q),(f:ℝ)) :=
      (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
        (by simpa only [DirichletCharacter.changeLevel_self,d] using
          norm_dirichlet_gauss_induced (dvd_refl q) χ n hn)
    _ ≤ Real.sqrt d*(∑ f∈m.divisors,(f:ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((m:ℝ)*(1+Real.log m)) :=
      mul_le_mul_of_nonneg_left (divisorSum_le_log m hmp) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((m:ℝ)*(1+Real.log q)) := by gcongr
    _ = _ := by
      change Real.sqrt (d:ℝ)*((m:ℝ)*(1+Real.log q)) =
        (q:ℝ)*(1+Real.log q)/Real.sqrt (d:ℝ)
      apply (eq_div_iff hroot.ne').2
      rw [hqR,← hs]
      ring

/-- The high-product-conductor part of the signed quadratic form has a
uniform square-root saving, independent of gcd(n,q). -/
theorem highProductConductorPacketBound
    (n : ℕ) (hn : 0<n) (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) (hD : 0<D) :
    ‖∑ χ∈S, ∑ ψ∈S.filter (fun ψ => D≤(χ*ψ).conductor),
       (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      ((q:ℝ)*(1+Real.log q)/Real.sqrt D)*(∑ χ∈S,‖w χ‖)^2 := by
  let K := (q:ℝ)*(1+Real.log q)/Real.sqrt D
  have hq1 : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hL : 0≤(q:ℝ)*(1+Real.log q) := by
    have := Real.log_nonneg hq1
    positivity
  have hK : 0≤K := div_nonneg hL (Real.sqrt_nonneg _)
  have hterm (χ ψ : DirichletCharacter ℂ q) (hψ : D≤(χ*ψ).conductor) :
      ‖(w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
        ‖w χ‖*‖w ψ‖*K := by
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (shiftedGauss_productConductor (χ*ψ) n hn).trans
    exact div_le_div_of_nonneg_left hL (Real.sqrt_pos.2 (by exact_mod_cast hD))
      (Real.sqrt_le_sqrt (by exact_mod_cast hψ))
  change _ ≤ K*(∑ χ∈S,‖w χ‖)^2
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S.filter (fun ψ => D≤(χ*ψ).conductor), ‖w χ‖*‖w ψ‖*K := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro χ _
      apply (norm_sum_le _ _).trans
      exact sum_le_sum fun ψ hψ => hterm χ ψ (mem_filter.mp hψ).2
    _ ≤ ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*K :=
      sum_le_sum fun χ _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

end
end InnerFloorResearch
