import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic


open Finset
open scoped Classical
namespace InnerFloorDensityPair
noncomputable section

/-- The density budget at a prescribed logarithmic cutoff.  No density
    theorem is asserted here: the accepted density bound supplies hden. -/
theorem densityBudget (X Q T δ c C M : ℝ)
    (hX : Real.exp 1 ≤ X) (hQ : 1 ≤ Q) (hT : 2 ≤ T)
    (hQX : Q ≤ X) (hlog : Real.log (Q*T) ≤ 2*Real.log X)
    (hδ : 0 ≤ δ) (hc : δ*Real.log X ≤ c*Real.log (Real.log X))
    (hC : 0 ≤ C)
    (hden : M ≤ C*(Q^2*T)^(3*δ/(1+δ))*Real.log (Q*T)^13) :
    M ≤ C*2^13*(Real.log X)^(9*c+13) := by
  have hX1 : 1 < X := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hXp : 0 < X := by linarith
  have hLp : 0 < Real.log X := Real.log_pos hX1
  have hQp : 0 < Q := by linarith
  have hTp : 0 < T := by linarith
  have hbase : 1 ≤ Q^2*T := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ) (by linarith)
  have hQT : Q*T ≤ X^2 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
  have hbaseX : Q^2*T ≤ X^3 := by
    calc
      _ = Q*(Q*T) := by ring
      _ ≤ X*(X^2) := mul_le_mul hQX hQT (by positivity) hXp.le
      _ = _ := by ring
  have hexp : 3*δ/(1+δ) ≤ 3*δ := div_le_self (by positivity) (by linarith)
  have hpower : (Q^2*T)^(3*δ/(1+δ)) ≤ (Real.log X)^(9*c) := by
    calc
      _ ≤ (Q^2*T)^(3*δ) := Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ ≤ (X^3)^(3*δ) := Real.rpow_le_rpow (by positivity) hbaseX (by positivity)
      _ = X^(9*δ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]; congr 1; norm_num; ring
      _ ≤ (Real.log X)^(9*c) := by
        rw [Real.rpow_def_of_pos hXp, Real.rpow_def_of_pos hLp]
        apply Real.exp_le_exp.mpr
        linarith only [hc]
  have hlog0 : 0 ≤ Real.log (Q*T) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQ (by linarith))
  have hlogpow : Real.log (Q*T)^13 ≤ (2*Real.log X)^13 := pow_le_pow_left₀ hlog0 hlog 13
  calc
    M ≤ _ := hden
    _ ≤ C*(Real.log X)^(9*c)*(2*Real.log X)^13 := by gcongr
    _ = _ := by
      have h13 : (Real.log X)^(13:ℝ) = (Real.log X)^(13:ℕ) := by
        simpa only [Nat.cast_ofNat] using (Real.rpow_natCast (Real.log X) 13)
      rw [mul_pow, Real.rpow_add hLp, h13]
      ring

/-- Ordered zero-pair occurrences, not distinct complex values: the product
    preserves multiplicity because the occurrence identifiers are retained. -/
theorem pairCard {ι : Type*} (s : Finset ι) (L K a : ℝ)
    (hL : 0<L) (hK : 0≤K) (hc : (s.card:ℝ) ≤ K*L^a) :
    ((s ×ˢ s).card:ℝ) ≤ K^2*L^(2*a) := by
  rw [Finset.card_product, Nat.cast_mul]
  calc
    _ ≤ (K*L^a)*(K*L^a) := mul_le_mul hc hc (by positivity) (by positivity)
    _ = _ := by
      rw [show 2*a=a+a by ring,Real.rpow_add hL]
      ring

/-- Absorb the fixed density constant into an extra log exponent eventually.
    This avoids assuming a cardinality bound with leading constant one. -/
theorem absorbPairConstant {ι : Type*} (s : Finset ι) (L K a : ℝ)
    (hL : 1≤L) (hK : 0≤K) (hK2 : K^2≤L)
    (hc : (s.card:ℝ)≤K*L^a) : ((s ×ˢ s).card:ℝ)≤L^(2*a+1) := by
  have hLp : 0<L := by linarith
  calc
    _ ≤ K^2*L^(2*a) := pairCard s L K a hLp hK hc
    _ ≤ L*L^(2*a) := mul_le_mul_of_nonneg_right hK2 (by positivity)
    _ = _ := by rw [Real.rpow_add hLp,Real.rpow_one];ring

end
end InnerFloorDensityPair
#print axioms InnerFloorDensityPair.densityBudget
#print axioms InnerFloorDensityPair.pairCard
#print axioms InnerFloorDensityPair.absorbPairConstant

namespace InnerFloorResidualThresholds
noncomputable section

/-- The conductors retained by the product gate have a concrete upper bound. -/
theorem productGate_exact (L k D : ℝ) (hL : 0<L) (hD : 0<D) :
    1 < L^k*(1/Real.sqrt D) ↔ D < L^(2*k) := by
  have hs : 0<Real.sqrt D := Real.sqrt_pos.2 hD
  have hl : 0<L^k := Real.rpow_pos_of_pos hL _
  rw [mul_one_div, lt_div_iff₀ hs, one_mul]
  rw [show 2*k=k+k by ring, Real.rpow_add hL, ← pow_two]
  constructor
  · intro h
    nlinarith [Real.sq_sqrt hD.le]
  · intro h
    by_contra! hh
    nlinarith [Real.sq_sqrt hD.le]

/-- The gcd gate leaves only pairs whose common level has a sufficiently
    large overlap with the target integer. -/
theorem gcdGate_exact (L k g : ℝ) (hL : 0<L) (hg : 0≤g) :
    1 < L^k*Real.sqrt g ↔ L^(-2*k)<g := by
  have hl : 0<L^k := Real.rpow_pos_of_pos hL _
  have hs := Real.sqrt_nonneg g
  have he : L^(-2*k)=(1/L^k)^2 := by
    rw [show -2*k = -(k+k) by ring, Real.rpow_neg hL.le, Real.rpow_add hL]
    ring
  rw [he, mul_comm (L^k) (Real.sqrt g), ← div_lt_iff₀ hl]
  exact Real.lt_sqrt (div_pos one_pos hl).le


/-- With the deliberately conservative global density budget, all pairs
    already inside the near-one cutoff can fail the real-part gate.  This
    records the precise limitation; the good-zero estimate is separate. -/
theorem nearOneDeficit (N δ c b d : ℝ) (hN : Real.exp 1≤N)
    (hc : δ*Real.log N≤c*Real.log (Real.log N))
    (hb : 1-δ<b) (hd : 1-δ<d) :
    (2-b-d)*Real.log N < 2*c*Real.log (Real.log N) := by
  have hlog : 0<Real.log N := Real.log_pos (by linarith [Real.add_one_le_exp (1:ℝ)])
  have h := mul_lt_mul_of_pos_right (show 2-b-d<2*δ by linarith) hlog
  linarith only [h,hc]

end
end InnerFloorResidualThresholds
#print axioms InnerFloorResidualThresholds.productGate_exact
#print axioms InnerFloorResidualThresholds.gcdGate_exact
#print axioms InnerFloorResidualThresholds.nearOneDeficit

namespace InnerFloorResidualScale
noncomputable section

/-- Explicit eventual scale to absorb the density constant: no unproved
    asymptotic claim is needed to remove the numeric side condition. -/
theorem eventualDensityConstant (K : ℝ) :
    ∃ X₀ : ℝ, 1≤X₀ ∧ ∀ X≥X₀,
      Real.exp 1≤X ∧ K^2≤1+Real.log X := by
  refine ⟨Real.exp (max 1 (K^2)), ?_, ?_⟩
  · exact Real.one_le_exp (by linarith [le_max_left (1:ℝ) (K^2)])
  · intro X hX
    have h1 : Real.exp 1≤X :=
      (Real.exp_le_exp.mpr (le_max_left _ _)).trans hX
    have hh := Real.log_le_log (Real.exp_pos (max 1 (K^2))) hX
    rw [Real.log_exp] at hh
    exact ⟨h1,by linarith [le_max_right (1:ℝ) (K^2)]⟩

/-- A log-budget summed over a finite number of blocks incurs exactly the
    corresponding extra power. Keeps the block residual sign unchanged. -/
theorem aggregateBlockFloor {ι : Type*} (s : Finset ι) (v w : ι→ℝ)
    (C N L m b : ℝ) (hC : 0≤C) (hN : 0≤N) (hL : 0<L)
    (hcard : (s.card:ℝ)≤L^b)
    (h : ∀ i∈s, w i-C*(N/L^(m+b))≤v i) :
    (∑ i∈s,w i)-C*(N/L^m)≤∑ i∈s,v i := by
  have hs := Finset.sum_le_sum h
  rw [Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hpos : 0≤C*(N/L^(m+b)) := by positivity
  have ht : (s.card:ℝ)*(C*(N/L^(m+b)))≤C*(N/L^m) := by
    calc
      _ ≤ L^b*(C*(N/L^(m+b))) := mul_le_mul_of_nonneg_right hcard hpos
      _ = _ := by
        rw [Real.rpow_add hL]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hL m), ne_of_gt (Real.rpow_pos_of_pos hL b)]
  linarith

end
end InnerFloorResidualScale
#print axioms InnerFloorResidualScale.eventualDensityConstant
#print axioms InnerFloorResidualScale.aggregateBlockFloor
