import Conjectures.Goldbach.InnerFloorPrimeWeightTransfer
import Conjectures.Goldbach.InnerFloorConductorLift

/-!
The analytic family of nonprincipal primitive characters is exactly the
arithmetic family filtered by nontriviality. Modulus one is accounted
for separately. No density assumption occurs in this finite identity.
-/
open Finset BombieriVinogradov.LargeSieve
open OAI.Ostmann
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def indexedNonprincipal (A : ℕ) : Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (Icc 1 A).sigma (fun q => (primitiveCharacters q).filter (fun χ => χ ≠ 1))

def analyticFamilyEmbedding (A : ℕ) :
    {p // p ∈ indexedNonprincipal A} ↪ PrimitiveComplexCharacter where
  toFun p :=
    let hp := Finset.mem_sigma.mp p.property
    let hc := Finset.mem_filter.mp hp.2
    ⟨p.val.1, (Finset.mem_Icc.mp hp.1).1, p.val.2,
      (Finset.mem_filter.mp hc.1).2, hc.2⟩
  inj' := by
    intro p r h
    apply Subtype.ext
    exact congrArg (fun χ : PrimitiveComplexCharacter =>
      (⟨χ.modulus, χ.character⟩ : Σ q : ℕ, DirichletCharacter ℂ q)) h

def analyticPrimitiveFamily (A : ℕ) : Finset PrimitiveComplexCharacter :=
  (indexedNonprincipal A).attach.map (analyticFamilyEmbedding A)

theorem analyticPrimitiveFamily_modulus (A : ℕ) :
    ∀ χ∈analyticPrimitiveFamily A, χ.modulus≤A := by
  intro χ hχ
  obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hχ
  exact (Finset.mem_Icc.mp (Finset.mem_sigma.mp p.property).1).2

theorem sum_analyticPrimitiveFamily (A : ℕ)
    (g : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    (∑ χ∈analyticPrimitiveFamily A,g χ.modulus χ.character) =
      ∑ q∈Icc 1 A, ∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1), g q χ := by
  unfold analyticPrimitiveFamily
  rw [Finset.sum_map]
  change (∑ p∈(indexedNonprincipal A).attach,g p.val.1 p.val.2) = _
  calc
    _ = ∑ p∈indexedNonprincipal A,g p.1 p.2 :=
      Finset.sum_attach (indexedNonprincipal A) (fun p => g p.1 p.2)
    _ = _ := by
      unfold indexedNonprincipal
      rw [Finset.sum_sigma]

/-- On every window, the primitive arithmetic energy is the sum of the
nonprincipal analytic family plus at most the single modulus-one term. -/
theorem primitiveEnergy_le_analyticFamily (A : ℕ) (y h : ℝ) :
    (∑ q∈Icc 1 A,primitivePrimeWindowEnergy q y h) ≤
      (∑ χ∈analyticPrimitiveFamily A,
        ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) +
      ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖^2 := by
  let g (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    ‖InnerFloorAP.centeredPrimeSum χ y h‖^2
  let P := ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖^2
  rw [sum_analyticPrimitiveFamily A g]
  have ht (q : ℕ) (hq : q∈Icc 1 A) :
      primitivePrimeWindowEnergy q y h ≤
        (∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1),g q χ) +
          (if q=1 then P else 0) := by
    change (∑ ψ∈primitiveCharacters q,g q ψ) ≤ _
    by_cases hmem : (1:DirichletCharacter ℂ q) ∈ primitiveCharacters q
    · have hprim : (1:DirichletCharacter ℂ q).IsPrimitive := (mem_filter.mp hmem).2
      have hq1 : q=1 := by
        letI : NeZero q := ⟨by have := (mem_Icc.mp hq).1; omega⟩
        simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hprim.symm
      subst q
      have he : (primitiveCharacters 1).filter (fun χ => χ ≠ 1) =
          (primitiveCharacters 1).erase 1 := by ext χ; simp [and_comm]
      rw [if_pos rfl]
      have hsum : (∑ χ∈(primitiveCharacters 1).filter (fun χ => χ ≠ 1),g 1 χ) =
          ∑ χ∈(primitiveCharacters 1).erase 1,g 1 χ :=
        congrArg (fun S : Finset (DirichletCharacter ℂ 1) => ∑ χ∈S,g 1 χ) he
      have hEq : (∑ χ∈primitiveCharacters 1,g 1 χ) =
          (∑ χ∈(primitiveCharacters 1).filter (fun χ => χ ≠ 1),g 1 χ)+P :=
        (sum_erase_add _ _ hmem).symm.trans
          (congrArg (fun z : ℝ => z+P) hsum.symm)
      exact hEq.le
    · have he : (primitiveCharacters q).filter (fun χ => χ ≠ 1) =
          primitiveCharacters q := by
        ext χ
        simp only [mem_filter]
        exact ⟨fun h => h.1,fun h => ⟨h,fun hc => hmem (hc ▸ h)⟩⟩
      have hsum : (∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1),g q χ) =
          ∑ χ∈primitiveCharacters q,g q χ :=
        congrArg (fun S : Finset (DirichletCharacter ℂ q) => ∑ χ∈S,g q χ) he
      rw [hsum]
      apply le_add_of_nonneg_right
      split_ifs <;> positivity
  calc
    _ ≤ ∑ q∈Icc 1 A,
      ((∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1),g q χ) +
        (if q=1 then P else 0)) := sum_le_sum ht
    _ = (∑ q∈Icc 1 A, ∑ χ∈(primitiveCharacters q).filter (fun χ => χ ≠ 1),g q χ) +
        (∑ q∈Icc 1 A, if q=1 then P else 0) := sum_add_distrib
    _ ≤ _ := by
      apply add_le_add_right
      rw [sum_ite_eq']
      split_ifs <;> first | exact le_rfl | exact sq_nonneg _

end
end InnerFloorResearch
