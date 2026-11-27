import Conjectures.Goldbach.InnerFloorProductConductor

/-!
Aggregate high-product-conductor weights over all common multiples.
Only finite arithmetic and the verified Gauss bound are used.
-/
open Finset InnerFloorLinearTotient
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem commonMultipleTotientWeight (A L : ℕ) (hL : 0 < L) (hLA : L ≤ A) :
    (∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) ≤
      (weightConstant*(1+Real.log A))^2 := by
  let F (d : ℕ) : ℝ := if d=L then L else 0
  have hF : ∀ d, 0≤F d := by intro d; dsimp [F]; split_ifs <;> positivity
  have hA : 0 < A := hL.trans_le hLA
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by exact_mod_cast hA)
  have hlogL : Real.log L ≤ Real.log A :=
    Real.log_le_log (by exact_mod_cast hL) (by exact_mod_cast hLA)
  have hLf : L ∈ Icc 1 A := mem_Icc.mpr ⟨hL,hLA⟩
  have hratio : (L:ℝ)/(L.totient:ℝ) ≤ weightConstant*(1+Real.log A) :=
    (ratio_totient_le L hL).trans (mul_le_mul_of_nonneg_left (by linarith)
      weightConstant_nonneg)
  have hrewrite :
      (∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) =
      ∑ q ∈ Icc 1 A, (∑ d ∈ q.divisors,F d)/(q.totient:ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro q hq
    have hq0 : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
    have hmem : L ∈ q.divisors ↔ L ∣ q := by simp [Nat.mem_divisors,hq0]
    by_cases hdiv : L ∣ q
    · have h := hmem.mpr hdiv
      simp [F,hdiv,h]
    · have h : L ∉ q.divisors := fun hm => hdiv (hmem.mp hm)
      simp [F,hdiv,h]
  have hsum : (∑ d ∈ Icc 1 A,F d/(d.totient:ℝ)) = (L:ℝ)/(L.totient:ℝ) := by
    simp [F,ite_div,hLf]
  rw [hrewrite]
  apply (sum_conductor_weights A F hF).trans
  rw [hsum,pow_two]
  exact mul_le_mul_of_nonneg_right hratio (mul_nonneg weightConstant_nonneg (by linarith))

def productCoefficient (q d₁ d₂ D : ℕ) : ℝ :=
  Real.sqrt d₁ * Real.sqrt d₂ * q * (1+Real.log q) /
    ((q.totient:ℝ)^2 * Real.sqrt D)

/-- At most four logarithms are lost when summing the high-product
conductor coefficient over all moduli divisible by both original
conductors. No assumption on gcd(n,q) occurs. -/
theorem productCoefficientFamily (A d₁ d₂ D : ℕ)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (hD : 0 < D) :
    (∑ q ∈ (Icc 1 A).filter (fun q => d₁ ∣ q ∧ d₂ ∣ q),
       productCoefficient q d₁ d₂ D) ≤
      weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  let L := Nat.lcm d₁ d₂
  have hL : 0 < L := Nat.lcm_pos h₁ h₂
  have hset :
      (Icc 1 A).filter (fun q => d₁ ∣ q ∧ d₂ ∣ q) =
        (Icc 1 A).filter (fun q => L ∣ q) := by
    ext q
    simp [L,Nat.lcm_dvd_iff]
  have hD' : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hD)
  have hd₁ : d₁ ≤ L := Nat.le_of_dvd hL (Nat.dvd_lcm_left d₁ d₂)
  have hd₂ : d₂ ≤ L := Nat.le_of_dvd hL (Nat.dvd_lcm_right d₁ d₂)
  have hroot : Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ) ≤ (L:ℝ) := by
    calc
      _ ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hd₁))
          (Real.sqrt_le_sqrt (by exact_mod_cast hd₂)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  by_cases hLA : L≤A
  · have hA : 0<A := hL.trans_le hLA
    have hlogA : 0≤Real.log A := Real.log_nonneg (by exact_mod_cast hA)
    let C := weightConstant*(1+Real.log A)^2/Real.sqrt D
    have hC : 0≤C := by
      dsimp [C]
      exact div_nonneg (mul_nonneg weightConstant_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
    have ht (q : ℕ) (hq : q∈(Icc 1 A).filter (fun q => L ∣ q)) :
        productCoefficient q d₁ d₂ D ≤ C*((L:ℝ)/(q.totient:ℝ)) := by
      have hq1 : 0<q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hqA := (mem_Icc.mp (mem_filter.mp hq).1).2
      have hlogq : 0≤Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have hlog : Real.log q≤Real.log A :=
        Real.log_le_log (by exact_mod_cast hq1) (by exact_mod_cast hqA)
      have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
      have hr : (q:ℝ)/(q.totient:ℝ) ≤ weightConstant*(1+Real.log A) :=
        (ratio_totient_le q hq1).trans
          (mul_le_mul_of_nonneg_left (by linarith) weightConstant_nonneg)
      calc
        _ = (Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ)/(q.totient:ℝ))*
            ((q:ℝ)/(q.totient:ℝ))*(1+Real.log q)/Real.sqrt D := by
          unfold productCoefficient
          ring
        _ ≤ ((L:ℝ)/(q.totient:ℝ))*(weightConstant*(1+Real.log A))*
            (1+Real.log A)/Real.sqrt D := by
          apply div_le_div_of_nonneg_right _ hD'.le
          apply mul_le_mul _ (by linarith) (by positivity)
            (mul_nonneg (by positivity) (mul_nonneg weightConstant_nonneg (by linarith)))
          exact mul_le_mul (div_le_div_of_nonneg_right hroot hφ.le) hr
            (by positivity) (by positivity)
        _ = _ := by dsimp [C]; ring
    rw [hset]
    calc
      _ ≤ ∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), C*((L:ℝ)/(q.totient:ℝ)) :=
        sum_le_sum ht
      _ = C*(∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) :=
        (mul_sum ..).symm
      _ ≤ C*(weightConstant*(1+Real.log A))^2 :=
        mul_le_mul_of_nonneg_left (commonMultipleTotientWeight A L hL hLA) hC
      _ = _ := by dsimp [C]; ring
  · have he : (Icc 1 A).filter (fun q => L ∣ q)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hq' := mem_filter.mp hq
      exact hLA ((Nat.le_of_dvd (mem_Icc.mp hq'.1).1 hq'.2).trans (mem_Icc.mp hq'.1).2)
    rw [hset,he,sum_empty]
    exact div_nonneg (mul_nonneg (pow_nonneg weightConstant_nonneg _) (by positivity)) (Real.sqrt_nonneg _)

end
end InnerFloorResearch
