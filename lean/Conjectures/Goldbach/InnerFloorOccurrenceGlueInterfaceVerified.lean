import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
/-! Diagnostic only: exact upstream types, with density as a typeclass INPUT.
Not an independent zero-density theorem, and not an official proof. -/
namespace OAI.Ostmann
open scoped Classical BigOperators
structure PrimitiveComplexCharacter where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℂ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
noncomputable def PrimitiveComplexCharacter.L (χ : PrimitiveComplexCharacter) : ℂ → ℂ :=
  @DirichletCharacter.LFunction χ.modulus ⟨χ.positive.ne'⟩ χ.character
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
structure ComplexZeroEnumeration (χ : PrimitiveComplexCharacter) where
  zeros : ℕ → ℂ
  in_strip : ∀ i, 0 < (zeros i).re ∧ (zeros i).re < 1
  actual_zero : ∀ i, χ.L (zeros i) = 0
  finite_height : ∀ T : ℝ, {i | |(zeros i).im| ≤ T}.Finite
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
noncomputable def ComplexZeroEnumeration.V14 {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) : Finset ℕ := (Z.finite_height T).toFinset
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
@[simp] theorem ComplexZeroEnumeration.V2r {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) (i : ℕ) :
    i ∈ Z.V14 T ↔ |(Z.zeros i).im| ≤ T := Set.Finite.mem_toFinset _
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
noncomputable def ComplexZeroEnumeration.count {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (σ T : ℝ) : ℕ :=
  ((Z.V14 T).filter (fun i => σ ≤ (Z.zeros i).re)).card
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
def V1gp (Z : ∀ χ, ComplexZeroEnumeration χ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ), 1 ≤ Q → ∀ (T σ : ℝ), 2 ≤ T →
    1 / 2 ≤ σ → σ ≤ 1 → ∀ F : Finset PrimitiveComplexCharacter,
    (∀ χ ∈ F, χ.modulus ≤ Q) →
    (∑ χ ∈ F, ((Z χ).count σ T : ℝ)) ≤
      C * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
        (Real.log ((Q : ℝ) * T)) ^ 13
class DensityInput where
  enumeration : ∀ χ, ComplexZeroEnumeration χ
  density : V1gp enumeration
noncomputable def V1 [d : DensityInput] (χ : PrimitiveComplexCharacter) := d.enumeration χ
theorem V1f0 [d : DensityInput] : V1gp V1 := d.density
end OAI.Ostmann
section Diagnostic
variable [OAI.Ostmann.DensityInput]




open scoped BigOperators
namespace InnerFloorResearch
noncomputable section

/-- A signed packet family can be reduced to the exceptional intersection of
all failed gates, retaining exact residual signs rather than replacing those
terms by their absolute values. The budgets apply only to the packet model. -/
theorem signedResidualPartition {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (P Q R : ι → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] (N L C r m : ℝ)
    (hN : 0 ≤ N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ L^r)
    (hP : ∀ i ∈ s, P i → ‖z i‖ ≤ C*(N/L^(m+r)))
    (hQ : ∀ i ∈ s, Q i → ‖z i‖ ≤ C*(N/L^(m+r)))
    (hR : ∀ i ∈ s, R i → ‖z i‖ ≤ C*(N/L^(m+r))) :
    (∑ i ∈ s.filter (fun i => ¬P i ∧ ¬Q i ∧ ¬R i), (z i).re) - C*(N/L^m)
      ≤ ∑ i ∈ s, (z i).re := by
  classical
  let G := s.filter (fun i => P i ∨ Q i ∨ R i)
  let B := s.filter (fun i => ¬P i ∧ ¬Q i ∧ ¬R i)
  have hG : G ⊆ s := Finset.filter_subset _ _
  have hdisj : Disjoint G B := by
    apply Finset.disjoint_left.mpr
    intro i hiG hiB
    have hg := (Finset.mem_filter.mp hiG).2
    have hb := (Finset.mem_filter.mp hiB).2
    rcases hg with h | h | h
    · exact hb.1 h
    · exact hb.2.1 h
    · exact hb.2.2 h
  have hcover : G ∪ B = s := by
    ext i
    simp only [G,B,Finset.mem_union,Finset.mem_filter]
    tauto
  have hpos : 0 ≤ C*(N/L^(m+r)) := by positivity
  have hsum : ∑ i ∈ G, ‖z i‖ ≤ C*(N/L^m) := by
    calc
      ∑ i ∈ G, ‖z i‖ ≤ ∑ _i ∈ G, C*(N/L^(m+r)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hs := hG hi
        rcases (Finset.mem_filter.mp hi).2 with h | h | h
        · exact hP i hs h
        · exact hQ i hs h
        · exact hR i hs h
      _ = (G.card:ℝ)*(C*(N/L^(m+r))) := by simp
      _ ≤ L^r*(C*(N/L^(m+r))) := by
        apply mul_le_mul_of_nonneg_right _ hpos
        exact (show (G.card:ℝ) ≤ (s.card:ℝ) by exact_mod_cast Finset.card_le_card hG).trans hcard
      _ = C*(N/L^m) := by
        rw [Real.rpow_add hL]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hL m), ne_of_gt (Real.rpow_pos_of_pos hL r)]
  have hgood : -(C*(N/L^m)) ≤ ∑ i ∈ G, (z i).re := by
    have hn : -(∑ i ∈ G, ‖z i‖) ≤ ∑ i ∈ G, (z i).re := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have habs := Complex.abs_re_le_norm (z i)
      exact (neg_le_neg habs).trans (neg_abs_le _)
    linarith
  have hsplit : ∑ i ∈ s, (z i).re = (∑ i ∈ G, (z i).re) + (∑ i ∈ B, (z i).re) := by
    rw [← hcover, Finset.sum_union hdisj]
  change (∑ i ∈ B, (z i).re) - C*(N/L^m) ≤ _
  linarith

end
end InnerFloorResearch
#print axioms InnerFloorResearch.signedResidualPartition

open scoped BigOperators
namespace InnerFloorResearch
noncomputable section

/-- Exponential form of the quantitative zero-pair deficit, retaining the
    logarithmic loss of the sparse family. This is a conditional numerical
    estimate only, not a zero-free region. -/
theorem sparseDeficitTerm (N L b c k m : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hgap : (k+m)*Real.log L ≤ (2-b-c)*Real.log N) :
    N^(b+c-1)*L^k ≤ N/L^m := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL m)).2
  rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hL,
    Real.rpow_def_of_pos hL, ← Real.exp_add, ← Real.exp_add]
  calc
    _ ≤ Real.exp (Real.log N) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hgap]
    _ = N := Real.exp_log hN

/-- A log-power-sized packet family is small when each pair has the required
    real-part deficit, without multiplying by the total number of moduli. -/
theorem sparseDeficitSum {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (N L C r k m : ℝ)
    (b c : ι → ℝ) (hN : 0 < N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ L^r)
    (hw : ∀ i ∈ s, w i ≤ C * (N^(b i+c i-1)*L^k))
    (hgap : ∀ i ∈ s, (k+(m+r))*Real.log L ≤ (2-b i-c i)*Real.log N) :
    ∑ i ∈ s, w i ≤ C*(N/L^m) := by
  have hden : 0 < L^(m+r) := Real.rpow_pos_of_pos hL _
  have hq : 0 ≤ C*(N/L^(m+r)) := mul_nonneg hC (div_nonneg hN.le hden.le)
  calc
    ∑ i ∈ s, w i ≤ ∑ _i ∈ s, C*(N/L^(m+r)) :=
      Finset.sum_le_sum fun i hi => (hw i hi).trans
        (mul_le_mul_of_nonneg_left (sparseDeficitTerm N L (b i) (c i) k (m+r) hN hL (hgap i hi)) hC)
    _ = (s.card : ℝ)*(C*(N/L^(m+r))) := by simp
    _ ≤ L^r*(C*(N/L^(m+r))) := mul_le_mul_of_nonneg_right hcard hq
    _ = C*(N/L^m) := by
      rw [Real.rpow_add hL]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hL m), ne_of_gt (Real.rpow_pos_of_pos hL r)]

end
end InnerFloorResearch
#print axioms InnerFloorResearch.sparseDeficitTerm
#print axioms InnerFloorResearch.sparseDeficitSum

namespace InnerFloorResearch
noncomputable section
open scoped BigOperators

/-- Convert a saving factor to an inverse logarithmic budget. -/
theorem packetSavingBudget (N L C b c k m r g : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C) (hg : 0 ≤ g)
    (hb : b+c ≤ 2) (hgate : L^(k+(m+r))*g ≤ 1) :
    C*(N^(b+c-1)*L^k)*g ≤ C*(N/L^(m+r)) := by
  have hn : 0 < N := by linarith
  have hpow : N^(b+c-1) ≤ N := by
    conv_rhs => rw [← Real.rpow_one N]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hLr : 0 < L^(m+r) := Real.rpow_pos_of_pos hL _
  have hsmall : L^k*g ≤ 1/L^(m+r) := by
    apply (le_div_iff₀ hLr).2
    rw [Real.rpow_add hL] at hgate
    linarith only [show L^k*g*L^(m+r) = L^k*L^(m+r)*g by ring,hgate]
  calc
    _ = C*(N^(b+c-1)*(L^k*g)) := by ring
    _ ≤ C*(N*(1/L^(m+r))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul hpow hsmall (by positivity) hn.le
    _ = _ := by ring

/-- All three quantitative mechanisms simultaneously.  The unsolved term is
exactly the intersection of their failure regions, not a signed estimate
for an unrelated union of arcs. -/
theorem quantitativeResidualPartition {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (b c u v : ι → ℝ) (N L C k r m : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card:ℝ) ≤ L^r)
    (hb : ∀ i ∈ s, b i+c i ≤ 2)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (h0 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k))
    (h1 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k)*u i)
    (h2 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k)*v i) :
    (∑ i ∈ s.filter (fun i =>
      (2-b i-c i)*Real.log N < (k+(m+r))*Real.log L ∧
      1 < L^(k+(m+r))*u i ∧ 1 < L^(k+(m+r))*v i), (z i).re)
      - C*(N/L^m) ≤ ∑ i ∈ s, (z i).re := by
  classical
  let P (i : ι) := (k+(m+r))*Real.log L ≤ (2-b i-c i)*Real.log N
  let Q (i : ι) := L^(k+(m+r))*u i ≤ 1
  let R (i : ι) := L^(k+(m+r))*v i ≤ 1
  have hn : 0 < N := by linarith
  have hP : ∀ i ∈ s, P i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hp
    exact (h0 i hi).trans (mul_le_mul_of_nonneg_left
      (sparseDeficitTerm N L (b i) (c i) k (m+r) hn hL hp) hC)
  have hQ : ∀ i ∈ s, Q i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hq
    exact (h1 i hi).trans (packetSavingBudget N L C (b i) (c i) k m r (u i) hN hL hC (hu i hi) (hb i hi) hq)
  have hR : ∀ i ∈ s, R i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hr
    exact (h2 i hi).trans (packetSavingBudget N L C (b i) (c i) k m r (v i) hN hL hC (hv i hi) (hb i hi) hr)
  simpa only [P,Q,R,not_le] using signedResidualPartition s z P Q R N L C r m
    hn.le hL hC hcard hP hQ hR

end
end InnerFloorResearch
#print axioms InnerFloorResearch.packetSavingBudget
#print axioms InnerFloorResearch.quantitativeResidualPartition

namespace InnerFloorDiagnostic
class ModelInput where
  constant : ℝ
  constant_nonneg : 0≤constant
  coefficient : ∀ {q : ℕ} [NeZero q], DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℕ → ℂ
  pair : ℝ → ℝ → ℝ → ℝ → ℂ → ℂ → ℝ → ℝ → ℂ
end InnerFloorDiagnostic
variable [InnerFloorDiagnostic.ModelInput]
namespace InnerFloorLinearTotient
noncomputable def weightConstant : ℝ := InnerFloorDiagnostic.ModelInput.constant
theorem weightConstant_nonneg : 0≤weightConstant := InnerFloorDiagnostic.ModelInput.constant_nonneg
end InnerFloorLinearTotient
namespace InnerFloorZeroModel
noncomputable def dyadicPair : ℝ → ℝ → ℝ → ℝ → ℂ → ℂ → ℝ → ℝ → ℂ := InnerFloorDiagnostic.ModelInput.pair
end InnerFloorZeroModel
namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorZeroModel
open scoped Classical
noncomputable section
noncomputable def signedCoefficient {q : ℕ} [NeZero q] : DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℕ → ℂ := InnerFloorDiagnostic.ModelInput.coefficient
structure DyadicPacket where
  level : ℕ
  level_pos : 0 < level
  χ : DirichletCharacter ℂ level
  ψ : DirichletCharacter ℂ level
  ρ : ℂ
  σ : ℂ
  S : Finset ℕ
  a : ℕ → ℝ
  b : ℕ → ℝ
  c : ℕ → ℝ
  d : ℕ → ℝ
  R : ℕ → ℝ

def DyadicPacket.value (p : DyadicPacket) (n : ℕ) : ℂ :=
  ∑ q∈p.S, (if h : 0 < q ∧ p.level ∣ q then
    letI : NeZero q := ⟨h.1.ne'⟩
    signedCoefficient (DirichletCharacter.changeLevel h.2 p.χ)
      (DirichletCharacter.changeLevel h.2 p.ψ) n else 0) *
    dyadicPair (p.a q) (p.b q) (p.c q) (p.d q) p.ρ p.σ (p.R q) n

def DyadicPacket.productSaving (p : DyadicPacket) : ℝ :=
  letI : NeZero p.level := ⟨p.level_pos.ne'⟩
  1 / Real.sqrt ((p.χ*p.ψ).conductor:ℝ)

def DyadicPacket.gcdSaving (p : DyadicPacket) (n : ℕ) : ℝ :=
  Real.sqrt ((Nat.gcd n p.level:ℝ)/(p.level:ℝ))

structure DyadicPacket.Admissible (p : DyadicPacket) (A : ℕ) (N : ℝ) : Prop where
  hLA : p.level ≤ A
  hS : p.S ⊆ (Icc 1 A).filter (fun q => p.level∣q)
  hρ : 3/4≤p.ρ.re
  hσ : 3/4≤p.σ.re
  hsum : p.ρ.re+p.σ.re≤2
  ha : ∀ q∈p.S, 0<p.a q
  hb : ∀ q∈p.S, p.a q≤p.b q+1
  hc : ∀ q∈p.S, 0<p.c q
  hd : ∀ q∈p.S, p.c q≤p.d q+1
  hbN : ∀ q∈p.S, p.b q+1≤N
  hdN : ∀ q∈p.S, p.d q+1≤N
  hR : ∀ q∈p.S, 0≤p.R q

class BoundInput where
  threeBounds (p : DyadicPacket) (A n : ℕ) (N : ℝ)
    (hn : 0<n) (hN : 1≤N) (hp : p.Admissible A N) :
    let B := (2*weightConstant^3)*(N^(p.ρ.re+p.σ.re-1)*(1+Real.log A)^(4:ℝ))
    ‖p.value n‖ ≤ B ∧ ‖p.value n‖ ≤ B*p.productSaving ∧
      ‖p.value n‖ ≤ B*p.gcdSaving n
variable [BoundInput]
theorem DyadicPacket.threeBounds (p : DyadicPacket) (A n : ℕ) (N : ℝ)
    (hn : 0<n) (hN : 1≤N) (hp : p.Admissible A N) :
    let B := (2*weightConstant^3)*(N^(p.ρ.re+p.σ.re-1)*(1+Real.log A)^(4:ℝ))
    ‖p.value n‖ ≤ B ∧ ‖p.value n‖ ≤ B*p.productSaving ∧
      ‖p.value n‖ ≤ B*p.gcdSaving n := BoundInput.threeBounds p A n N hn hN hp
end
end InnerFloorGaussPacket
variable [InnerFloorGaussPacket.BoundInput]


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
namespace InnerFloorOccurrence
open Finset OAI.Ostmann InnerFloorGaussPacket InnerFloorLinearTotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

abbrev Pair := Occurrence × Occurrence

def pairLevel (ij : Pair) : ℕ := Nat.lcm ij.1.1.modulus ij.2.1.modulus

theorem pairLevel_pos (ij : Pair) : 0 < pairLevel ij :=
  Nat.lcm_pos ij.1.1.positive ij.2.1.positive

/-- The common denominator is the lcm, not an arbitrary input level. -/
def packet (ij : Pair) (S : Finset ℕ) (a b c d R : ℕ→ℝ) : DyadicPacket where
  level := pairLevel ij
  level_pos := pairLevel_pos ij
  χ := DirichletCharacter.changeLevel (Nat.dvd_lcm_left _ _) ij.1.1.character
  ψ := DirichletCharacter.changeLevel (Nat.dvd_lcm_right _ _) ij.2.1.character
  ρ := zero ij.1
  σ := zero ij.2
  S := S.filter (fun q => pairLevel ij ∣ q)
  a := a
  b := b
  c := c
  d := d
  R := R

/-- Two successive lifts are the direct lift of the original characters. -/
theorem packet_lift_left (ij : Pair) (S : Finset ℕ) (a b c d R : ℕ→ℝ)
    {q : ℕ} (h : pairLevel ij ∣ q) :
    DirichletCharacter.changeLevel h (packet ij S a b c d R).χ =
      DirichletCharacter.changeLevel ((Nat.dvd_lcm_left ij.1.1.modulus ij.2.1.modulus).trans h) ij.1.1.character := by
  exact (DirichletCharacter.changeLevel_trans ij.1.1.character _ h).symm

theorem packet_lift_right (ij : Pair) (S : Finset ℕ) (a b c d R : ℕ→ℝ)
    {q : ℕ} (h : pairLevel ij ∣ q) :
    DirichletCharacter.changeLevel h (packet ij S a b c d R).ψ =
      DirichletCharacter.changeLevel ((Nat.dvd_lcm_right ij.1.1.modulus ij.2.1.modulus).trans h) ij.2.1.character := by
  exact (DirichletCharacter.changeLevel_trans ij.2.1.character _ h).symm

/-- Common log scale: A can be much smaller than N. We only use
    log A ≤ log N, never identify these two scales. -/
theorem packetThreeBoundsAtScale (p : DyadicPacket) (A n : ℕ) (N : ℝ)
    (hA : 1≤A) (hAN : (A:ℝ)≤N) (hn : 0<n) (hN : 1≤N)
    (hp : p.Admissible A N) :
    let B := (2*weightConstant^3)*(N^(p.ρ.re+p.σ.re-1)*(1+Real.log N)^(4:ℝ))
    ‖p.value n‖ ≤ B ∧ ‖p.value n‖ ≤ B*p.productSaving ∧
      ‖p.value n‖ ≤ B*p.gcdSaving n := by
  have h := p.threeBounds A n N hn hN hp
  dsimp only at h ⊢
  have hA1 : (1:ℝ)≤A := by exact_mod_cast hA
  have hlog : 0≤1+Real.log A := by linarith [Real.log_nonneg hA1]
  have hb : 1+Real.log A≤1+Real.log N := by
    linarith [Real.log_le_log (show (0:ℝ)<A by linarith) hAN]
  have hp4 : (1+Real.log A)^(4:ℝ)≤(1+Real.log N)^(4:ℝ) :=
    Real.rpow_le_rpow hlog hb (by norm_num)
  have hC : 0≤2*weightConstant^3 := mul_nonneg (by norm_num) (pow_nonneg weightConstant_nonneg 3)
  have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp4
    (Real.rpow_nonneg (by linarith : 0≤N) (p.ρ.re+p.σ.re-1))) hC
  exact ⟨h.1.trans hb',h.2.1.trans (mul_le_mul_of_nonneg_right hb' (by unfold DyadicPacket.productSaving; positivity)),
    h.2.2.trans (mul_le_mul_of_nonneg_right hb' (by unfold DyadicPacket.gcdSaving; positivity))⟩

/-- End-to-end density to signed residual, with original zero occurrences,
    common-level lifts and a single explicit log scale.  The windows and
    finite primitive-character family are inputs from the spectral expansion. -/
theorem occurrenceResidual : ∃ K : ℝ, 0<K ∧
    ∀ (F : Finset PrimitiveComplexCharacter) (A n : ℕ) (N T δ c₀ m : ℝ),
      1≤A → 0<n → Real.exp 1≤N → 2≤T → (A:ℝ)≤N →
      Real.log ((A:ℝ)*T)≤2*Real.log N → 0≤δ → δ≤1/4 →
      δ*Real.log N≤c₀*Real.log (Real.log N) → 0≤c₀ → K^2≤1+Real.log N →
      (∀ χ∈F, χ.modulus≤A) →
      ∀ (S : Finset ℕ) (a b c d R : Pair→ℕ→ℝ),
      S ⊆ Icc 1 A →
      (∀ ij∈pairs F δ T A, ∀ q∈S, 0<a ij q ∧ a ij q≤b ij q+1 ∧
        0<c ij q ∧ c ij q≤d ij q+1 ∧ b ij q+1≤N ∧ d ij q+1≤N ∧ 0≤R ij q) →
      let L := 1+Real.log N
      let r := 2*(9*c₀+13)+1
      let s := pairs F δ T A
      let p := fun ij => packet ij S (a ij) (b ij) (c ij) (d ij) (R ij)
      (∑ ij∈s.filter (fun ij =>
        (2-(zero ij.1).re-(zero ij.2).re)*Real.log N < (4+(m+r))*Real.log L ∧
        1 < L^(4+(m+r))*(p ij).productSaving ∧
        1 < L^(4+(m+r))*(p ij).gcdSaving n), ((p ij).value n).re)
        -(2*weightConstant^3)*(N/L^m) ≤ ∑ ij∈s, ((p ij).value n).re := by
  obtain ⟨K,hK,hbudget⟩ := occurrenceBudget
  refine ⟨K,hK,?_⟩
  intro F A n N T δ c₀ m hA hn hN hT hAN hlog hδ hδ' hcut hc₀ hK2 hF S a b c d R hS hw
  dsimp only
  let L := 1+Real.log N
  let r := 2*(9*c₀+13)+1
  let s := pairs F δ T A
  let p := fun ij => packet ij S (a ij) (b ij) (c ij) (d ij) (R ij)
  have hN1 : 1≤N := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hlogN : 1≤Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hN
  have hL : 1≤L := by dsimp [L]; linarith
  have hLp : 0<L := by linarith
  have hc : ((occurrences F δ T).card:ℝ)≤K*L^(9*c₀+13) := by
    apply (hbudget F A N T δ c₀ hA hN hT hAN hlog hδ (by linarith) hcut hF).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.rpow_le_rpow (by linarith : 0≤Real.log N) (by dsimp [L]; linarith)
    linarith
  have hcard : (s.card:ℝ)≤L^r := pairBudget A hL hK.le hK2 hc
  have hadm : ∀ ij∈s, (p ij).Admissible A N := by
    intro ij hij
    have hnz := pairNearOne hij hδ'
    constructor
    · exact hnz.2.2.2
    · intro q hq
      have h := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hS h.1,h.2⟩
    · exact hnz.1
    · exact hnz.2.1
    · exact hnz.2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.2.2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.2.2.2.2
  apply InnerFloorResearch.quantitativeResidualPartition s (fun ij => (p ij).value n)
    (fun ij => (zero ij.1).re) (fun ij => (zero ij.2).re)
    (fun ij => (p ij).productSaving) (fun ij => (p ij).gcdSaving n)
    N L (2*weightConstant^3) 4 r m hN1 hLp
    (mul_nonneg (by norm_num) (pow_nonneg weightConstant_nonneg 3)) hcard
  · intro ij hi; exact (hadm ij hi).hsum
  · intro ij hi; unfold DyadicPacket.productSaving; positivity
  · intro ij hi; unfold DyadicPacket.gcdSaving; positivity
  · intro ij hi; exact (packetThreeBoundsAtScale (p ij) A n N hA hAN hn hN1 (hadm ij hi)).1
  · intro ij hi; exact (packetThreeBoundsAtScale (p ij) A n N hA hAN hn hN1 (hadm ij hi)).2.1
  · intro ij hi; exact (packetThreeBoundsAtScale (p ij) A n N hA hAN hn hN1 (hadm ij hi)).2.2

end
end InnerFloorOccurrence
#print axioms InnerFloorOccurrence.packet_lift_left
#print axioms InnerFloorOccurrence.packet_lift_right
#print axioms InnerFloorOccurrence.packetThreeBoundsAtScale
#print axioms InnerFloorOccurrence.occurrenceResidual

namespace InnerFloorOccurrence
open Finset OAI.Ostmann InnerFloorGaussPacket InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

/-- Denominator-first term using the original primitive characters, not
    independently chosen characters at the common level. -/
def denominatorTerm (ij : Pair) (q n : ℕ) (a b c d R : ℕ→ℝ) : ℂ :=
  (if h : 0<q ∧ pairLevel ij∣q then
    letI : NeZero q := ⟨h.1.ne'⟩
    signedCoefficient
      (DirichletCharacter.changeLevel ((Nat.dvd_lcm_left ij.1.1.modulus ij.2.1.modulus).trans h.2) ij.1.1.character)
      (DirichletCharacter.changeLevel ((Nat.dvd_lcm_right ij.1.1.modulus ij.2.1.modulus).trans h.2) ij.2.1.character) n
  else 0) * dyadicPair (a q) (b q) (c q) (d q) (zero ij.1) (zero ij.2) (R q) n

/-- Pair packet equals sum of original-character terms over all denominators.
    Terms at incompatible denominators are exactly zero. -/
theorem packet_value_eq (ij : Pair) (S : Finset ℕ) (n : ℕ) (a b c d R : ℕ→ℝ) :
    (packet ij S a b c d R).value n = ∑ q∈S, denominatorTerm ij q n a b c d R := by
  unfold DyadicPacket.value
  change (∑ q∈S.filter (fun q => pairLevel ij∣q),
    (if h : 0<q ∧ pairLevel ij∣q then
      letI : NeZero q := ⟨h.1.ne'⟩
      signedCoefficient
        (DirichletCharacter.changeLevel h.2
          (DirichletCharacter.changeLevel (Nat.dvd_lcm_left ij.1.1.modulus ij.2.1.modulus) ij.1.1.character))
        (DirichletCharacter.changeLevel h.2
          (DirichletCharacter.changeLevel (Nat.dvd_lcm_right ij.1.1.modulus ij.2.1.modulus) ij.2.1.character)) n
    else 0) * dyadicPair (a q) (b q) (c q) (d q) (zero ij.1) (zero ij.2) (R q) n) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : pairLevel ij∣q
  · rw [if_pos h]
    unfold denominatorTerm
    by_cases hq0 : 0<q
    · have hh : 0<q ∧ pairLevel ij∣q := ⟨hq0,h⟩
      simp only [dif_pos hh]
      letI : NeZero q := ⟨hq0.ne'⟩
      exact congrArg₂ (fun x y : DirichletCharacter ℂ q =>
        signedCoefficient x y n * dyadicPair (a q) (b q) (c q) (d q) (zero ij.1) (zero ij.2) (R q) n)
        (packet_lift_left ij S a b c d R h) (packet_lift_right ij S a b c d R h)
    · have hh : ¬(0<q ∧ pairLevel ij∣q) := fun ht => hq0 ht.1
      simp only [dif_neg hh]
  · rw [if_neg h]
    unfold denominatorTerm
    have hh : ¬(0<q ∧ pairLevel ij∣q) := fun ht => h ht.2
    rw [dif_neg hh,zero_mul]

/-- Exact interchange of denominator-first and pair-first sums, including
    elimination of lcm>A pairs, with no loss or cancellation assumed. -/
theorem reindexDenominatorSum (F : Finset PrimitiveComplexCharacter)
    (δ T : ℝ) (A n : ℕ) (S : Finset ℕ)
    (a b c d R : Pair→ℕ→ℝ) (hS : S⊆Icc 1 A) :
    (∑ q∈S, ∑ ij∈(occurrences F δ T) ×ˢ (occurrences F δ T),
      denominatorTerm ij q n (a ij) (b ij) (c ij) (d ij) (R ij)) =
    ∑ ij∈pairs F δ T A, (packet ij S (a ij) (b ij) (c ij) (d ij) (R ij)).value n := by
  rw [Finset.sum_comm]
  unfold pairs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases h : Nat.lcm ij.1.1.modulus ij.2.1.modulus≤A
  · rw [if_pos h]
    exact (packet_value_eq ij S n (a ij) (b ij) (c ij) (d ij) (R ij)).symm
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro q hq
    unfold denominatorTerm
    have hq' := Finset.mem_Icc.mp (hS hq)
    rw [dif_neg (fun hh => h ((Nat.le_of_dvd (by omega : 0<q) hh.2).trans hq'.2)),zero_mul]

end
end InnerFloorOccurrence
#print axioms InnerFloorOccurrence.packet_value_eq
#print axioms InnerFloorOccurrence.reindexDenominatorSum

namespace InnerFloorOccurrence
open Finset OAI.Ostmann InnerFloorGaussPacket InnerFloorLinearTotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

/-- Final aggregation interface, in the denominator-first order used by
    the prime spectral expansion. The only untreated part is the signed
    triple-gate intersection of genuine near-one zero occurrences. -/
theorem denominatorResidualFloor : ∃ K : ℝ, 0<K ∧
    ∀ (F : Finset PrimitiveComplexCharacter) (A n : ℕ) (N T δ c₀ m : ℝ),
      1≤A → 0<n → Real.exp 1≤N → 2≤T → (A:ℝ)≤N →
      Real.log ((A:ℝ)*T)≤2*Real.log N → 0≤δ → δ≤1/4 →
      δ*Real.log N≤c₀*Real.log (Real.log N) → 0≤c₀ → K^2≤1+Real.log N →
      (∀ χ∈F, χ.modulus≤A) →
      ∀ (S : Finset ℕ) (a b c d R : Pair→ℕ→ℝ),
      S ⊆ Icc 1 A →
      (∀ ij∈pairs F δ T A, ∀ q∈S, 0<a ij q ∧ a ij q≤b ij q+1 ∧
        0<c ij q ∧ c ij q≤d ij q+1 ∧ b ij q+1≤N ∧ d ij q+1≤N ∧ 0≤R ij q) →
      let L := 1+Real.log N
      let r := 2*(9*c₀+13)+1
      let s := pairs F δ T A
      let p := fun ij => packet ij S (a ij) (b ij) (c ij) (d ij) (R ij)
      (∑ ij∈s.filter (fun ij =>
        (2-(zero ij.1).re-(zero ij.2).re)*Real.log N < (4+(m+r))*Real.log L ∧
        1 < L^(4+(m+r))*(p ij).productSaving ∧
        1 < L^(4+(m+r))*(p ij).gcdSaving n), ((p ij).value n).re)
        -(2*weightConstant^3)*(N/L^m) ≤
      (∑ q∈S, ∑ ij∈(occurrences F δ T) ×ˢ (occurrences F δ T),
        denominatorTerm ij q n (a ij) (b ij) (c ij) (d ij) (R ij)).re := by
  obtain ⟨K,hK,H⟩ := occurrenceResidual
  refine ⟨K,hK,?_⟩
  intro F A n N T δ c₀ m hA hn hN hT hAN hlog hδ hδ' hcut hc₀ hK2 hF S a b c d R hS hw
  dsimp only
  rw [reindexDenominatorSum F δ T A n S a b c d R hS]
  rw [Complex.re_sum]
  exact H F A n N T δ c₀ m hA hn hN hT hAN hlog hδ hδ' hcut hc₀ hK2 hF S a b c d R hS hw

end
end InnerFloorOccurrence
#print axioms InnerFloorOccurrence.denominatorResidualFloor

end Diagnostic
