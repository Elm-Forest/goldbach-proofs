import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

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


open Finset OAI.Ostmann
open scoped Classical
namespace InnerFloorOccurrence
noncomputable section

abbrev Occurrence := Σ _χ : PrimitiveComplexCharacter, ℕ

def nearOneIndices (δ T : ℝ) (χ : PrimitiveComplexCharacter) : Finset ℕ :=
  ((V1 χ).V14 T).filter (fun i => 1-δ < ((V1 χ).zeros i).re)

def occurrences (F : Finset PrimitiveComplexCharacter) (δ T : ℝ) : Finset Occurrence :=
  F.sigma (nearOneIndices δ T)

def pairs (F : Finset PrimitiveComplexCharacter) (δ T : ℝ) (A : ℕ) :
    Finset (Occurrence × Occurrence) :=
  ((occurrences F δ T) ×ˢ (occurrences F δ T)).filter
    (fun ij => Nat.lcm ij.1.1.modulus ij.2.1.modulus ≤ A)

def zero (i : Occurrence) : ℂ := (V1 i.1).zeros i.2

theorem occurrence_in_strip (i : Occurrence) : 0 < (zero i).re ∧ (zero i).re < 1 :=
  (V1 i.1).in_strip i.2

theorem occurrence_actual_zero (i : Occurrence) : i.1.L (zero i) = 0 :=
  (V1 i.1).actual_zero i.2

theorem occurrenceNearOne {F : Finset PrimitiveComplexCharacter} {δ T : ℝ}
    {i : Occurrence} (hi : i∈occurrences F δ T) :
    i.1∈F ∧ |(zero i).im|≤T ∧ 1-δ < (zero i).re := by
  have h := Finset.mem_sigma.mp hi
  have h' := Finset.mem_filter.mp h.2
  exact ⟨h.1, ((V1 i.1).V2r T i.2).mp h'.1, h'.2⟩

/-- Every actual occurrence is counted by the accepted density theorem V1f0;
    the index, rather than its complex value, preserves multiplicities. -/
theorem occurrenceBudget : ∃ K : ℝ, 0<K ∧
    ∀ (F : Finset PrimitiveComplexCharacter) (Q : ℕ) (X T δ c : ℝ),
      1≤Q → Real.exp 1≤X → 2≤T → (Q:ℝ)≤X →
      Real.log ((Q:ℝ)*T)≤2*Real.log X → 0≤δ → δ≤1/2 →
      δ*Real.log X≤c*Real.log (Real.log X) →
      (∀ χ∈F, χ.modulus≤Q) →
      ((occurrences F δ T).card:ℝ)≤K*(Real.log X)^(9*c+13) := by
  obtain ⟨C,hC,hden⟩ := V1f0
  refine ⟨C*2^13,by positivity,?_⟩
  intro F Q X T δ c hQ hX hT hQX hlog hδ hδ' hc hF
  have hcard : ((occurrences F δ T).card:ℝ) ≤
      ∑ χ∈F, ((V1 χ).count (1-δ) T:ℝ) := by
    rw [occurrences,Finset.card_sigma,Nat.cast_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    apply Nat.cast_le.mpr
    unfold nearOneIndices ComplexZeroEnumeration.count
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2.le⟩
  have hd := hden Q hQ T (1-δ) hT (by linarith) (by linarith) F hF
  rw [show (1:ℝ)-(1-δ)=δ by ring,show (2:ℝ)-(1-δ)=1+δ by ring] at hd
  exact InnerFloorDensityPair.densityBudget X Q T δ c C ((occurrences F δ T).card:ℝ)
    hX (by exact_mod_cast hQ) hT hQX hlog hδ hc hC.le (hcard.trans hd)

/-- Filter out pairs that cannot have any common denominator in the range.
    Pair indexing still distinguishes repeated occurrences. -/
theorem pairBudget {F : Finset PrimitiveComplexCharacter} {δ T L K a : ℝ}
    (A : ℕ) (hL : 1≤L) (hK : 0≤K) (hK2 : K^2≤L)
    (hcard : ((occurrences F δ T).card:ℝ)≤K*L^a) :
    ((pairs F δ T A).card:ℝ)≤L^(2*a+1) := by
  have hs : pairs F δ T A ⊆ (occurrences F δ T) ×ˢ (occurrences F δ T) :=
    Finset.filter_subset _ _
  exact (show ((pairs F δ T A).card:ℝ)≤(((occurrences F δ T) ×ˢ (occurrences F δ T)).card:ℝ) by
    exact_mod_cast Finset.card_le_card hs).trans
    (InnerFloorDensityPair.absorbPairConstant (occurrences F δ T) L K a hL hK hK2 hcard)

/-- No low-product/conductor gate is used in the counting stage. -/
theorem pairNearOne {F : Finset PrimitiveComplexCharacter} {δ T : ℝ} {A : ℕ}
    {ij : Occurrence × Occurrence} (hi : ij∈pairs F δ T A) (hδ : δ≤1/4) :
    3/4≤(zero ij.1).re ∧ 3/4≤(zero ij.2).re ∧
    (zero ij.1).re+(zero ij.2).re≤2 ∧
    Nat.lcm ij.1.1.modulus ij.2.1.modulus≤A := by
  have h := Finset.mem_filter.mp hi
  have hp := Finset.mem_product.mp h.1
  have h₁ := (occurrenceNearOne hp.1).2.2
  have h₂ := (occurrenceNearOne hp.2).2.2
  exact ⟨by linarith,by linarith,by linarith [(occurrence_in_strip ij.1).2,(occurrence_in_strip ij.2).2],h.2⟩

end
end InnerFloorOccurrence
#print axioms InnerFloorOccurrence.occurrenceBudget
#print axioms InnerFloorOccurrence.pairBudget
#print axioms InnerFloorOccurrence.pairNearOne
