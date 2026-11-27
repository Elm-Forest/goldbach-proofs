import Conjectures.Goldbach.InnerFloorProductFamily

/-!
Retain both the product conductor and the gcd of the shift with the
imprimitive part of the modulus. All estimates are unconditional.
-/
open Finset DyadicMixedB4CharacterFactorBound
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

variable {q : ℕ} [NeZero q]

theorem shiftedGauss_gcdBound (χ : DirichletCharacter ℂ q) (n : ℕ)
    (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt χ.conductor * (Nat.gcd n (q/χ.conductor):ℝ) *
        (1+Real.log (Nat.gcd n (q/χ.conductor))) := by
  let d := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hm' : q/d=m := by
    rw [hm,Nat.mul_comm,Nat.mul_div_cancel _ hdp]
  let g := Nat.gcd n m
  have hgp : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hsub : n.divisors.filter (fun f => d*f ∣ q) ⊆ g.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    have hfm := Nat.dvd_of_mul_dvd_mul_left hdp hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd
      (Nat.dvd_of_mem_divisors (mem_filter.mp hf).1) hfm,hgp.ne'⟩
  change _ ≤ Real.sqrt d * (Nat.gcd n (q/d):ℝ) * _
  rw [hm']
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f ∣ q),(f:ℝ)) :=
      (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
        (by simpa only [DirichletCharacter.changeLevel_self,d] using
          norm_dirichlet_gauss_induced (dvd_refl q) χ n hn)
    _ ≤ Real.sqrt d*(∑ f∈g.divisors,(f:ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((g:ℝ)*(1+Real.log g)) :=
      mul_le_mul_of_nonneg_left (divisorSum_le_log g hgp) (Real.sqrt_nonneg _)
    _ = _ := by dsimp [g,d]; ring

/-- A general bound using gcd(n,q) rather than the full modulus, useful
for small product conductor. -/
theorem shiftedGauss_smallProduct (χ : DirichletCharacter ℂ q) (n D : ℕ)
    (hn : 0 < n) (hD : χ.conductor ≤ D) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q) := by
  let g := Nat.gcd n (q/χ.conductor)
  have hgp : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hgg : g ∣ Nat.gcd n q := Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    ((Nat.gcd_dvd_right _ _).trans (Nat.div_dvd_of_dvd χ.conductor_dvd_level))
  have hgq : g≤q := Nat.le_of_dvd (NeZero.pos q) (hgg.trans (Nat.gcd_dvd_right _ _))
  have hgg' : g≤Nat.gcd n q := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn) hgg
  have hL : 0≤Real.log g := Real.log_nonneg (by exact_mod_cast hgp)
  have hl := Real.log_le_log (by exact_mod_cast hgp : 0 < (g:ℝ)) (by exact_mod_cast hgq)
  calc
    _ ≤ Real.sqrt χ.conductor*(g:ℝ)*(1+Real.log g) :=
      shiftedGauss_gcdBound χ n hn
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hD))
          (by exact_mod_cast hgg') (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      · linarith
      · linarith
      · positivity

/-- The low-product-conductor part of a packet also has a saving when
gcd(n,q) is small. No coprimality assumption is necessary. -/
theorem lowProductGcdPacketBound (n : ℕ) (hn : 0 < n)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) :
    ‖∑ χ∈S, ∑ ψ∈S.filter (fun ψ => (χ*ψ).conductor≤D),
        (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q))*(∑ χ∈S,‖w χ‖)^2 := by
  let K := Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q)
  have hq1 : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hK : 0≤K := by
    dsimp [K]
    have := Real.log_nonneg hq1
    positivity
  have hterm (χ ψ : DirichletCharacter ℂ q) (hψ : (χ*ψ).conductor≤D) :
      ‖(w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
        ‖w χ‖*‖w ψ‖*K := by
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact shiftedGauss_smallProduct (χ*ψ) n D hn hψ
  change _ ≤ K*(∑ χ∈S,‖w χ‖)^2
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S.filter (fun ψ => (χ*ψ).conductor≤D), ‖w χ‖*‖w ψ‖*K := by
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
