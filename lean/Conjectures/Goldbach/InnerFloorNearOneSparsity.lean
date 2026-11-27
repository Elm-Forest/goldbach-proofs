import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
Unconditional sparsity of the near-one zeros left over after the existing
good-zero mean-square estimate. No fixed zero-free strip is assumed.
The cardinality bound alone does not establish their signed contribution.
-/

open Finset
open scoped Classical
open OAI.Ostmann V1l
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

def nearOneOccurrences (A : ℕ) (X T : ℝ)
    (χ : PrimitiveComplexCharacter) : Finset ℕ :=
  ((V1 χ).V14 T).filter (fun i => 1-V2j A X < ((V1 χ).zeros i).re)

/-- The bad part of the truncated primitive zero spectrum contains only
polylogarithmically many occurrences, across ALL moduli up to Q.
The cutoff is exactly the one used by the accepted mean-square theorem. -/
theorem nearOneOccurrencesCard (A : ℕ) :
    ∃ C : ℝ, 0<C ∧
      ∀ (Q : ℕ) (X T : ℝ),
      1≤Q → Real.exp 1≤X → 2≤T → (Q:ℝ)≤X →
      Real.log ((Q:ℝ)*T)≤2*Real.log X →
      0≤V2j A X → V2j A X≤1/2 →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      (∑ χ∈F, ((nearOneOccurrences A X T χ).card : ℝ)) ≤
        C*(Real.log X)^(27*(A+14)+13) := by
  obtain ⟨C,hC,hden⟩ := V1f0
  refine ⟨C*2^13,by positivity,?_⟩
  intro Q X T hQ hX hT hQX hlog hδ hδ' F hF
  let δ := V2j A X
  let L := Real.log X
  have hX1 : 1<X := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hXp : 0<X := by linarith
  have hLp : 0<L := Real.log_pos hX1
  have hL1 : 1≤L := by
    dsimp [L]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hq : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hq0 : (0:ℝ)<Q := by linarith
  have ht0 : 0<T := by linarith
  have hbase : 1≤(Q:ℝ)^2*T :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) (by linarith)
  have hQT : (Q:ℝ)*T≤X^2 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
  have hbaseX : (Q:ℝ)^2*T≤X^3 := by
    calc
      _ = (Q:ℝ)*((Q:ℝ)*T) := by ring
      _ ≤ X*(X^2) := mul_le_mul hQX hQT (by positivity) hXp.le
      _ = _ := by ring
  have hσ0 : (1/2:ℝ)≤1-δ := by dsimp [δ]; linarith
  have hσ1 : 1-δ≤1 := by dsimp [δ]; linarith
  have hcounts :
      (∑ χ∈F, ((nearOneOccurrences A X T χ).card : ℝ)) ≤
        ∑ χ∈F, ((V1 χ).count (1-δ) T : ℝ) := by
    apply sum_le_sum
    intro χ hχ
    apply Nat.cast_le.mpr
    unfold nearOneOccurrences ComplexZeroEnumeration.count
    apply card_le_card
    intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1,(mem_filter.mp hi).2.le⟩
  have hden' := hden Q hQ T (1-δ) hT hσ0 hσ1 F hF
  have hexp : 3*(1-(1-δ))/(2-(1-δ)) ≤ 3*δ := by
    rw [show (1:ℝ)-(1-δ)=δ by ring,show (2:ℝ)-(1-δ)=1+δ by ring]
    exact div_le_self (by dsimp [δ]; positivity) (by dsimp [δ]; linarith)
  have hpower : ((Q:ℝ)^2*T)^(3*(1-(1-δ))/(2-(1-δ))) ≤ L^(27*(A+14)) := by
    calc
      _ ≤ ((Q:ℝ)^2*T)^(3*δ) := Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ ≤ (X^3)^(3*δ) := Real.rpow_le_rpow (by positivity) hbaseX (by dsimp [δ]; positivity)
      _ = X^(9*δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
        congr 1
        norm_num
        ring
      _ = L^(27*(A+14)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hXp, Real.rpow_def_of_pos hLp]
        congr 1
        dsimp [δ,L,V2j]
        field_simp [ne_of_gt hLp]
        push_cast
        <;> ring
  have hlog0 : 0≤Real.log ((Q:ℝ)*T) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  have hlogpow : Real.log ((Q:ℝ)*T)^13 ≤ (2*L)^13 :=
    pow_le_pow_left₀ hlog0 hlog 13
  calc
    _ ≤ _ := hcounts
    _ ≤ _ := hden'
    _ ≤ C*L^(27*(A+14))*(2*L)^13 := by gcongr
    _ = _ := by rw [mul_pow,pow_add]; ring

end
end InnerFloorResearch
