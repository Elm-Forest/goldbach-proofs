import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor
import Conjectures.Goldbach.ReflectionCharacterContraction
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4
import Conjectures.Goldbach.LowSkirtFromShortProgressions
import PEqualNP.Outside.L_goldbach_frontier_medcore_bv_band

/-!
# Route B Pre-PR Unified Single-File Assembly for `L-goldbach-wide-remainder-inner-floor`

This self-contained single-file assembly achieves a **true single-gap closure**
for `L-goldbach-wide-remainder-inner-floor` with 0 `sorry`, 0 GRH imports, and
standard 3 axioms (`propext`, `Classical.choice`, `Quot.sound`) only:

- **Part I (`InnerFloorResearch`)**: Unconditional reduction of the exact frozen
  statement `FrozenWideRemainderInnerFloor` to the one-sided signed middle-band
  remainder floor `SignedMiddleRemainderFloor` (`candidate_of_signedMiddleFloor`),
  completely eliminating the two-sided L² energy requirement `MiddleCellEnergySmall`.
- **Part II (Route B Signed Toolkit & Independent Odd-Residual Modules)**:
  Occurrence residual reduction, signed bilinear cell floor, primitive quadratic
  Gauss sum evaluation, real-zero log-gap vs. super-log-gap threshold criterion,
  almost-all high-gcd measure bound, four-gate residual partition, global parity
  annihilation for composite even Siegel characters (`d = 3p`, `n = 2p^8`),
  odd squarefree totient tail (`≤ 2/3`), localized cross saving, real power-kernel
  scalar bound, and relative sign scalar floor.
- **Part III (`Conjectures.Goldbach`)**: Top-level entry point
  `L_goldbach_wide_remainder_inner_floor_of_signedMiddleFloor`.
-/

section PartI_SignedFrozenReduction

/-! Research-only conditional candidate; no external zero-free strip assumed proven.
Generated from individually reviewed research modules.
Retain source attribution in each original body. -/

/-! BEGIN InnerFloorArithmeticCore.lean; sha256 c0b88eb71935e24c8dccec78b5acf9336458b379349ed642e85f1a97f0870139 -/
section
/-!
Small independently replayable arithmetic interface extracted from
ShortProgressionsMeanTheta (XBribo, PR #3789,
a546c6629fae0223b56067d5e4ebc34043c4fbf1, Apache-2.0).
Names relocated to avoid duplicate OAI.Ostmann declarations when used
with DyadicCellShortPrimeFloor. Only elementary definitions and lemmas
are copied; none of the analytic black-box conclusions are assumed.
-/
open Finset Filter
open scoped Topology Classical
noncomputable section
namespace InnerFloorAP
def theta (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) : ℝ :=
  ∑ k ∈ (Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊).filter (fun k : ℕ => (k : ZMod q) = r),
    if k.Prime then Real.log (k : ℝ) else 0

theorem mem_window {y h : ℝ} (hy : 0 ≤ y) (hh : 0 ≤ h) (k : ℕ) :
    k ∈ Finset.Icc (⌊y⌋₊ + 1) ⌊y+h⌋₊ ↔ y < (k : ℝ) ∧ (k : ℝ) ≤ y+h := by
  rw [Finset.mem_Icc, Nat.add_one_le_iff, Nat.floor_lt hy, Nat.le_floor_iff (by linarith)]

def centeredPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (y h : ℝ) : ℂ :=
  (∑ k ∈ Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊,
    ((if k.Prime then Real.log (k : ℝ) else 0 : ℝ) : ℂ) * χ (k : ZMod q)) -
    (if χ = 1 then (h : ℂ) else 0)

theorem centeredPrimeSum_changeLevel {d q : ℕ} [NeZero q] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) {h y : ℝ} (hq : (q : ℝ) ≤ y) (hh : 0 ≤ h) :
    centeredPrimeSum (DirichletCharacter.changeLevel hd χ) y h = centeredPrimeSum χ y h := by
  classical
  have hone : DirichletCharacter.changeLevel hd χ = 1 ↔ χ = 1 := by
    rw [← map_one (DirichletCharacter.changeLevel (R := ℂ) hd)]
    exact (DirichletCharacter.changeLevel_injective hd).eq_iff
  unfold centeredPrimeSum
  simp only [hone]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpr : p.Prime
  · have hpy := ((mem_window ((Nat.cast_nonneg q).trans hq) hh p).1 hp).1
    have hqp : q < p := by exact_mod_cast (hq.trans_lt hpy)
    have hcop := hpr.coprime_iff_not_dvd.mpr
      (fun hdvd => (Nat.not_le_of_gt hqp) (Nat.le_of_dvd (NeZero.pos q) hdvd))
    have he := χ.changeLevel_eq_cast_of_dvd' hd (Nat.isCoprime_iff_coprime.mpr hcop)
    simpa only [Int.cast_natCast] using congrArg
      (fun z : ℂ => ((if p.Prime then Real.log (p : ℝ) else 0 : ℝ) : ℂ) * z) he
  · simp [hpr]


end InnerFloorAP

namespace InnerFloorLinearTotient
set_option maxHeartbeats 1000000 in


private def squareMass : ℝ := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
set_option maxHeartbeats 1000000 in

private theorem squareMass_nonneg : 0 ≤ squareMass := tsum_nonneg fun _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem sum_square_inv_le (s : Finset ℕ) :
    (∑ n ∈ s, ((n:ℝ)^2)⁻¹) ≤ squareMass :=
  (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2:ℕ))).sum_le_tsum s fun _ _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem one_le_squareMass : 1 ≤ squareMass := by
  simpa using sum_square_inv_le {(1:ℕ)}

set_option maxHeartbeats 1000000 in
/-- Uniform constant for the reciprocal-totient mean and conductor lifting. -/
def weightConstant : ℝ := Real.exp (2*squareMass) * squareMass
set_option maxHeartbeats 1000000 in

theorem weightConstant_nonneg : 0 ≤ weightConstant :=
  mul_nonneg (Real.exp_pos _).le squareMass_nonneg
set_option maxHeartbeats 1000000 in

private theorem prime_factor_bound {p : ℕ} (hp : 2 ≤ p) :
    (1-(p:ℝ)⁻¹)⁻¹ ≤ (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) := by
  let u := (p:ℝ)⁻¹
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu' : u ≤ 1/2 := by
    change (p:ℝ)⁻¹ ≤ 1/2
    rw [← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hp'
  have hden : 0 < 1-u := by linarith
  have hsq : u^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hu hu' 2
  have hnon := mul_nonneg (sq_nonneg u) (show 0 ≤ 1-2*u^2 by linarith)
  rw [← inv_pow]
  change (1-u)⁻¹ ≤ (1+u)*(1+2*u^2)
  rw [← one_div, div_le_iff₀ hden]
  nlinarith only [hnon]
set_option maxHeartbeats 1000000 in

private theorem squarefree_product_eq (q : ℕ) (hq : 0 < q) :
    (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) = ∑ d ∈ q.divisors with Squarefree d, (d:ℝ)⁻¹ := by
  rw [Finset.prod_one_add, Nat.sum_divisors_filter_squarefree hq.ne', Nat.factors_eq]
  refine sum_congr rfl fun s _ => ?_
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
  rw [Finset.prod_eq_multiset_prod, show (fun i : ℕ => i) = id from rfl, Multiset.map_id]
set_option maxHeartbeats 1000000 in

private theorem ratio_le_divisors (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hEuler : (q.totient:ℝ) = (q:ℝ)*∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹) := by
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀] using
      congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors q)
  have hlocal (p : ℕ) (hp : p ∈ q.primeFactors) : 0 ≤ (1-(p:ℝ)⁻¹)⁻¹ := by
    have hp' : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    apply inv_nonneg.mpr
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by linarith)
  have hsq : (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) ≤ Real.exp (2*squareMass) := by
    apply (Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)).trans
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_square_inv_le _) (by norm_num)
  calc
    _ = ∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹)⁻¹ := by
      rw [hEuler, div_mul_eq_div_div, div_self hq'.ne', one_div, Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) :=
      prod_le_prod₀ hlocal fun p hp => prime_factor_bound (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) :=
      Finset.prod_mul_distrib
    _ ≤ (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * Real.exp (2*squareMass) :=
      mul_le_mul_of_nonneg_left hsq (prod_nonneg fun _ _ => by positivity)
    _ ≤ _ := by
      rw [mul_comm, squarefree_product_eq q hq]
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)) (Real.exp_pos _).le
set_option maxHeartbeats 1000000 in

private theorem harmonic_bound (Q : ℕ) :
    (∑ i ∈ Icc 1 Q, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log Q

set_option maxHeartbeats 1000000 in
/-- Pointwise `q/φ(q)` also costs at most one logarithm. -/
theorem ratio_totient_le (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ weightConstant * (1+Real.log q) := by
  have hsub : q.divisors ⊆ Icc 1 q := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)⟩
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q from hq))
  calc
    _ ≤ Real.exp (2*squareMass) * (1+Real.log q) :=
      (ratio_le_divisors q hq).trans (mul_le_mul_of_nonneg_left
        ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (harmonic_bound q))
        (Real.exp_pos _).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (Real.exp_pos _).le one_le_squareMass) (by positivity)
set_option maxHeartbeats 1000000 in

private theorem sum_antidiagonal_le_product (Q : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal, f ab.1*g ab.2) ≤
      (∑ a ∈ Icc 1 Q, f a)*(∑ b ∈ Icc 1 Q, g b) := by
  let S := Icc 1 Q
  let w (p : ℕ × ℕ) := f p.1*g p.2
  have hw (p : ℕ × ℕ) : 0 ≤ w p := mul_nonneg (hf _) (hg _)
  have hsub (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal ⊆ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    intro ab hab
    have hm (d : ℕ) (hd : d ∈ q.divisors) : d ∈ S :=
      mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd (mem_Icc.mp hq).1 (Nat.dvd_of_mem_divisors hd)).trans (mem_Icc.mp hq).2⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
      hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
  change (∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab) ≤ _
  calc
    _ ≤ ∑ q ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w p :=
      sum_le_sum fun q hq => sum_le_sum_of_subset_of_nonneg (hsub q hq) (fun p _ _ => hw p)
    _ = ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w p :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ S ×ˢ S, w p := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hw p)
    _ = (∑ a ∈ S, f a)*(∑ b ∈ S, g b) := by rw [sum_product, sum_mul_sum]
set_option maxHeartbeats 1000000 in

private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1/(q.totient:ℝ) ≤ Real.exp (2*squareMass) *
      ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  calc
    _ = ((q:ℝ)/(q.totient:ℝ))/q := by
      rw [div_right_comm, div_self hq'.ne']
    _ ≤ (Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹)/q :=
      div_le_div_of_nonneg_right (ratio_le_divisors q hq) hq'.le
    _ = _ := by
      rw [mul_div_assoc, Finset.sum_div,
        ← Nat.sum_divisorsAntidiagonal (fun d _ => (d:ℝ)⁻¹/q) (n := q)]
      congr 1
      refine sum_congr rfl fun p hp => ?_
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul, div_eq_mul_inv,
        mul_inv, ← inv_pow, pow_two, mul_assoc]

set_option maxHeartbeats 1000000 in
/-- The sum of reciprocal totients costs one logarithm, uniformly in `Q`. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1/(q.totient:ℝ)) ≤ weightConstant * (1+Real.log Q) := by
  calc
    _ ≤ Real.exp (2*squareMass) * (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal,
        ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1
    _ ≤ Real.exp (2*squareMass) * ((∑ a ∈ Icc 1 Q, ((a:ℝ)^2)⁻¹)*(∑ b ∈ Icc 1 Q, (b:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (sum_antidiagonal_le_product Q (fun a => ((a:ℝ)^2)⁻¹) (fun b => (b:ℝ)⁻¹)
        (fun _ => by positivity) (fun _ => by positivity)) (Real.exp_pos _).le
    _ ≤ Real.exp (2*squareMass) * (squareMass*(1+Real.log Q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (sum_square_inv_le _) (harmonic_bound Q)
        (sum_nonneg fun _ _ => by positivity) squareMass_nonneg) (Real.exp_pos _).le
    _ = _ := (mul_assoc ..).symm

set_option maxHeartbeats 1000000 in
/-- Conductor multiplicities lose a single logarithm, including `d = 1`. -/
theorem sum_conductor_weights (Q : ℕ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ q ∈ Icc 1 Q, (∑ d ∈ q.divisors, F d)/(q.totient:ℝ)) ≤
      (∑ d ∈ Icc 1 Q, F d/(d.totient:ℝ)) * (weightConstant*(1+Real.log Q)) := by
  let f (d : ℕ) := F d/(d.totient:ℝ)
  let g (m : ℕ) := 1/(m.totient:ℝ)
  have hf (d : ℕ) : 0 ≤ f d := div_nonneg (hF d) (Nat.cast_nonneg _)
  have hg (m : ℕ) : 0 ≤ g m := by dsimp [g]; positivity
  have hterm (q : ℕ) : (∑ d ∈ q.divisors, F d)/(q.totient:ℝ) ≤
      ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := by
    rw [Finset.sum_div, ← Nat.sum_divisorsAntidiagonal (fun d _ => F d/(q.totient:ℝ)) (n := q)]
    refine sum_le_sum fun p hp => ?_
    have h1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have h2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    have h3 : 0 < (p.1.totient:ℝ)*(p.2.totient:ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.totient_pos.mpr h1) (Nat.totient_pos.mpr h2)
    have hφ := Nat.totient_super_multiplicative p.1 p.2
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1] at hφ
    calc
      _ ≤ F p.1/((p.1.totient:ℝ)*(p.2.totient:ℝ)) :=
        div_le_div_of_nonneg_left (hF _) h3 (by exact_mod_cast hφ)
      _ = _ := by
        simp only [f, g, div_eq_mul_inv, one_mul, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := sum_le_sum fun q _ => hterm q
    _ ≤ (∑ d ∈ Icc 1 Q, f d)*(∑ m ∈ Icc 1 Q, g m) := sum_antidiagonal_le_product Q f g hf hg
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_totient_le Q) (sum_nonneg fun d _ => hf d)


end InnerFloorLinearTotient

end

end

/-! BEGIN InnerFloorPrimeWeightTransfer.lean; sha256 e0fe19fd388e2875008d291af7c349de679243e607af5bb0c94ebb053e00177e -/
section
/-!
Transfer from von Mangoldt windows to logarithmic prime windows, preserving
the character index and family squared-energy budget. This is independent
of zero-free assumptions and does not assert a bound on the zero sum.
-/

open Finset ArithmeticFunction MeasureTheory
open scoped Interval Classical
open OAI.Ostmann V7e V2h
namespace InnerFloorResearch
noncomputable section

def logPrimeWeight (k : ℕ) : ℝ :=
  if k.Prime then Real.log k else 0

theorem logPrimeWeight_le_vonMangoldt (k : ℕ) :
    logPrimeWeight k ≤ vonMangoldt k := by
  by_cases hk : k.Prime
  · simp [logPrimeWeight,hk,vonMangoldt_apply_prime hk]
  · simp [logPrimeWeight,hk]

/-- An arbitrary bounded multiplier cannot amplify the total proper
prime-power mass on any subset of the prefix. -/
theorem weightedPrimePowerError (s : Finset ℕ) (X : ℝ)
    (hsub : s ⊆ Ioc 0 ⌊X⌋₊) (a : ℕ → ℂ)
    (ha : ∀ k ∈ s, ‖a k‖ ≤ 1) :
    ‖(∑ k∈s, (vonMangoldt k:ℂ)*a k) -
      (∑ k∈s, (logPrimeWeight k:ℂ)*a k)‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  have htotal :
      (∑ k∈Ioc 0 ⌊X⌋₊, (vonMangoldt k-logPrimeWeight k)) =
        Chebyshev.psi X-Chebyshev.theta X := by
    simp only [sum_sub_distrib,Chebyshev.psi,Chebyshev.theta,sum_filter,logPrimeWeight]
  rw [← sum_sub_distrib,← htotal]
  calc
    _ ≤ ∑ k∈s, ‖(vonMangoldt k:ℂ)*a k-(logPrimeWeight k:ℂ)*a k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k∈s, (vonMangoldt k-logPrimeWeight k) := by
      apply sum_le_sum
      intro k hk
      rw [← sub_mul,← Complex.ofReal_sub,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k))]
      exact mul_le_of_le_one_right (sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k)) (ha k hk)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => sub_nonneg.mpr (logPrimeWeight_le_vonMangoldt k))

/-- Exact identification of the floor-based integer-length window. -/
theorem windowIndices_eq (y : ℝ) (h : ℕ) (hy : 0 ≤ y) :
    V9a h y = Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
  rw [V9a,Nat.floor_add_natCast hy h]
  ext k
  simp only [mem_Ioc,mem_Icc,Nat.add_one_le_iff]

theorem centeredPrimeWindowError (χ : PrimitiveComplexCharacter)
    {X y : ℝ} (h : ℕ) (hy : 0 ≤ y) (hX : y+(h:ℝ) ≤ X) :
    ‖V4q χ h y - InnerFloorAP.centeredPrimeSum χ.character y h‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  let s := V9a h y
  have hsub : s ⊆ Ioc 0 ⌊X⌋₊ := by
    intro k hk
    have hm : k∈Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
      simpa only [s,windowIndices_eq y h hy] using hk
    have hk' := (InnerFloorAP.mem_window hy (Nat.cast_nonneg h) k).mp hm
    exact mem_Ioc.mpr ⟨by exact_mod_cast hy.trans_lt hk'.1,
      (Nat.le_floor_iff (by linarith [Nat.cast_nonneg (α := ℝ) h])).2 (hk'.2.trans hX)⟩
  have he := weightedPrimePowerError s X hsub
    (fun k => χ.character (k:ZMod χ.modulus))
    (fun k _ => DirichletCharacter.norm_le_one _ _)
  unfold V4q InnerFloorAP.centeredPrimeSum
  rw [if_neg χ.nontrivial,sub_zero,← windowIndices_eq y h hy]
  simp only [Vl,mul_comm (χ.character _),logPrimeWeight] at he ⊢
  exact he

/-- The family error is at most O(Q² X² log² X) on [X,2X],
using the uniform proper-prime-power mass bound and the primitive
character cardinality estimate. -/
theorem primitivePrimeWindowErrorEnergy (F : Finset PrimitiveComplexCharacter)
    (Q h : ℕ) {X : ℝ} (hX : 1≤X) (hh : (h:ℝ)≤X)
    (hF : ∀ χ∈F, χ.modulus≤Q) :
    (∑ χ∈F, ∫ y in X..2*X,
      ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
      X*(Q:ℝ)^2*(2*Real.sqrt (3*X)*Real.log (3*X))^2 := by
  let M := 2*Real.sqrt (3*X)*Real.log (3*X)
  have hM : 0≤M := by
    have hl : 0≤Real.log (3*X) := Real.log_nonneg (by linarith)
    dsimp [M]
    positivity
  have hterm (χ : PrimitiveComplexCharacter) :
      (∫ y in X..2*X, ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        X*M^2 := by
    have hXX : X≤2*X := by linarith
    rw [intervalIntegral.integral_of_le hXX]
    have hb : ∀ y∈Set.Ioc X (2*X),
        ‖V4q χ h y-InnerFloorAP.centeredPrimeSum χ.character y h‖^2≤M^2 := by
      intro y hy
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      exact (centeredPrimeWindowError χ h (by linarith [hy.1])
        (by linarith [hy.2])).trans (Chebyshev.psi_sub_theta_le (by linarith))
    calc
      _ ≤ ∫ _y in Set.Ioc X (2*X), M^2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
          (integrableOn_const (by simp)) (by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
            exact hb y hy)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hXX,intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  calc
    _ ≤ ∑ _χ∈F, X*M^2 := sum_le_sum fun χ _ => hterm χ
    _ = (F.card:ℝ)*(X*M^2) := by simp [nsmul_eq_mul]
    _ ≤ _ := by
      have hc : (F.card:ℝ)≤(Q:ℝ)^2 := by exact_mod_cast V14i F Q hF
      have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0≤X*M^2)
      dsimp [M] at *
      nlinarith only [hm]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorReducedGaussEnergy.lean; sha256 5679806f7783b3070a00d5c314d56348a3222f63907d83a536c10ec2a3d0ac68 -/
section
/-!
Research-only reduced-numerator projection for the inner-remainder problem.
Unlike the full additive Parseval bound (which pays q for every character),
this theorem pays the conductor of each character. It is an exact finite
identity followed by the already verified conductor-sensitive Gauss bound.
No prime distribution assumption is included.
-/

open Finset
open scoped Classical
namespace InnerFloorResearch
noncomputable section

variable {q : ℕ} [NeZero q]

open DyadicMixedB4RamanujanCharacters
open DyadicMixedB4CharacterFactorBound
open Conjectures.Goldbach.ReflectionCharacterContraction_aux

def unitAdditiveError (b : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) : ℂ :=
  ∑ r : (ZMod q)ˣ, b r * ZMod.stdAddChar ((a : ZMod q) * (r : ZMod q))

def unitCharacterError (b : (ZMod q)ˣ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ r : (ZMod q)ˣ, b r * χ (r : ZMod q)

theorem reducedSynthesis (b : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    unitAdditiveError b a =
      ∑ χ : DirichletCharacter ℂ q,
        (gaussSum χ⁻¹ ZMod.stdAddChar * unitCharacterError b χ /
          (q.totient : ℂ)) * χ (a : ZMod q) := by
  have hExp (r : (ZMod q)ˣ) :
      ZMod.stdAddChar ((a : ZMod q) * (r : ZMod q)) =
        (∑ χ : DirichletCharacter ℂ q,
          (χ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) *
            χ (a : ZMod q)) / (q.totient : ℂ) := by
    have hFintype :
        DyadicMixedB4RamanujanCharacters.unitFintype q =
          (inferInstance : Fintype (ZMod q)ˣ) := Subsingleton.elim _ _
    have h := unit_character_expansion
      (fun x : (ZMod q)ˣ => ZMod.stdAddChar ((x : ZMod q) * (r : ZMod q))) a
    rw [hFintype] at h
    have ht (χ : DirichletCharacter ℂ q) :
        (∑ x : (ZMod q)ˣ, star (χ (x : ZMod q)) *
          ZMod.stdAddChar ((x : ZMod q) * (r : ZMod q))) =
          χ (r : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
      have h' := unit_twisted_gauss χ (1 : (ZMod q)ˣ) r
      rw [hFintype] at h'
      simpa only [Units.val_one, one_mul, map_one] using h' 
    simpa only [ht] using h
  unfold unitAdditiveError
  simp_rw [hExp, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  unfold unitCharacterError
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem reducedGaussEnergy (b : (ZMod q)ˣ → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖unitAdditiveError b a‖^2) =
      (∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖^2 * ‖unitCharacterError b χ‖^2) /
        (q.totient : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  simp_rw [reducedSynthesis]
  rw [synth_norm]
  simp only [norm_div, norm_mul, Complex.norm_natCast, Nat.cast_ofNat, mul_pow]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro χ _
  field_simp

theorem reducedConductorEnergy (b : (ZMod q)ˣ → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖unitAdditiveError b a‖^2) ≤
      (∑ χ : DirichletCharacter ℂ q,
        (χ.conductor : ℝ) * ‖unitCharacterError b χ‖^2) /
        (q.totient : ℝ) := by
  rw [reducedGaussEnergy]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro χ _
  have hg := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at hg
  have hs := pow_le_pow_left₀ (norm_nonneg _) hg 2
  rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hs
  exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorConductorLift.lean; sha256 5d27e5673abcc38957a96f379096c1f778d2d2ff05f0f7b98b5ef127f81197d3 -/
section
/-!
Reduced-numerator conductor aggregation. This is an auxiliary research
statement and does not assume or assert the unproved primitive mean square.
The accepted ShortProgressionsMeanTheta module supplies the exact conductor
lifting for interior prime windows and the reciprocal-totient estimates.
-/

open Finset
open scoped Classical
namespace InnerFloorResearch
noncomputable section

open BombieriVinogradov.LargeSieve
open DyadicMixedB4ConductorPartition
open Conjectures.Goldbach.ReflectionCharacterContraction_aux

def reducedLevelEnergy (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : (ZMod q)ˣ, ‖unitAdditiveError (b q) a‖^2

/-- Only logarithmic conductor multiplicity is paid in the reduced projection.
F d is an arbitrary primitive-family energy budget. -/
theorem reducedFamilyEnergy (A : ℕ)
    (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d)
    (hcompat : ∀ (q : ℕ) [NeZero q], q ≤ A →
      ∀ (d : ℕ) (hd : d ∣ q),
        (∑ ψ ∈ primitiveCharacters d,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2) ≤ F d) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy b q) ≤
      (∑ d ∈ Icc 1 A, (d : ℝ)*F d/(d.totient : ℝ)) *
        (InnerFloorLinearTotient.weightConstant*(1+Real.log A)) := by
  have hterm (q : ℕ) (hq : q ∈ Icc 1 A) :
      reducedLevelEnergy b q ≤ (∑ d ∈ q.divisors, (d : ℝ)*F d)/(q.totient : ℝ) := by
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0.ne'⟩
    simp only [reducedLevelEnergy, dif_neg hq0.ne']
    apply (reducedConductorEnergy (b q)).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [sum_conductor_partition]
    rw [← Finset.sum_attach q.divisors (fun d => (d : ℝ)*F d)]
    apply sum_le_sum
    intro d _
    have hd : d.1 ∣ q := (Nat.mem_divisors.mp d.2).1
    calc
      _ = (d.1 : ℝ) * ∑ ψ ∈ primitiveCharacters d.1,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2 := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro ψ hψ
        have hp : ψ.IsPrimitive := (mem_filter.mp hψ).2
        rw [(DirichletCharacter.conductor_changeLevel ψ hd).trans hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcompat q (mem_Icc.mp hq).2 d.1 hd)
        (Nat.cast_nonneg _)
  exact (sum_le_sum hterm).trans
    (InnerFloorLinearTotient.sum_conductor_weights A (fun d => (d : ℝ)*F d)
      (fun d => mul_nonneg (Nat.cast_nonneg _) (hF d)))

/-- Two logarithms, rather than a polynomial factor in A, suffice to lift
a primitive squared-error budget to reduced-numerator energy. -/
theorem reducedFamilyEnergyLog (A : ℕ)
    (b : (q : ℕ) → (ZMod q)ˣ → ℂ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d)
    (hcompat : ∀ (q : ℕ) [NeZero q], q ≤ A →
      ∀ (d : ℕ) (hd : d ∣ q),
        (∑ ψ ∈ primitiveCharacters d,
          ‖unitCharacterError (b q) (DirichletCharacter.changeLevel hd ψ)‖^2) ≤ F d) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy b q) ≤
      (InnerFloorLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d ∈ Icc 1 A, F d := by
  let W := InnerFloorLinearTotient.weightConstant
  let L := 1 + Real.log A
  have hW : 0 ≤ W := InnerFloorLinearTotient.weightConstant_nonneg
  have hL : 0 ≤ L := by
    dsimp [L]
    linarith [Real.log_natCast_nonneg A]
  have hs : (∑ d ∈ Icc 1 A, (d : ℝ)*F d/(d.totient : ℝ)) ≤
      (W*L)*(∑ d ∈ Icc 1 A, F d) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have h := InnerFloorLinearTotient.ratio_totient_le d (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdA : (d : ℝ) ≤ A := by exact_mod_cast (mem_Icc.mp hd).2
    have hl := Real.log_le_log hd0 hdA
    have h' : (d : ℝ)/(d.totient : ℝ) ≤ W*L :=
      h.trans (mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) hW)
    calc
      _ = ((d : ℝ)/(d.totient : ℝ))*F d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h' (hF d)
  calc
    _ ≤ _ := reducedFamilyEnergy A b F hF hcompat
    _ ≤ ((W*L)*(∑ d ∈ Icc 1 A, F d))*(W*L) :=
      mul_le_mul_of_nonneg_right hs (mul_nonneg hW hL)
    _ = _ := by dsimp [W,L]; ring

def primeWindowResidueError (q : ℕ) (y h : ℝ) (r : (ZMod q)ˣ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (InnerFloorAP.theta q (r : ZMod q) y h : ℂ) -
      ((h/(q.totient : ℝ) : ℝ) : ℂ)

theorem primeWindowCharacterError {q : ℕ} [NeZero q] (y h : ℝ)
    (χ : DirichletCharacter ℂ q) :
    unitCharacterError (primeWindowResidueError q y h) χ =
      InnerFloorAP.centeredPrimeSum χ y h := by
  classical
  unfold unitCharacterError InnerFloorAP.centeredPrimeSum
  simp only [primeWindowResidueError, dif_neg (NeZero.ne q), sub_mul, sum_sub_distrib]
  congr 1
  · rw [sum_units_eq_sum
      (fun r : ZMod q => (InnerFloorAP.theta q r y h : ℂ)*χ r)
      (fun r hr => by rw [MulChar.map_nonunit χ hr, mul_zero])]
    simp only [InnerFloorAP.theta, Complex.ofReal_sum, sum_filter, apply_ite,
      Complex.ofReal_zero, sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    simp
  · rw [← Finset.mul_sum, sum_char_units]
    by_cases hc : χ = 1
    · rw [if_pos hc, if_pos hc]
      push_cast
      have hφ : (q.totient : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
      field_simp
    · simp [hc]

def primitivePrimeWindowEnergy (d : ℕ) (y h : ℝ) : ℝ :=
  ∑ ψ ∈ primitiveCharacters d, ‖InnerFloorAP.centeredPrimeSum ψ y h‖^2

theorem primeWindowReducedFamilyEnergy (A : ℕ) (y h : ℝ)
    (hy : (A : ℝ) ≤ y) (hh : 0 ≤ h) :
    (∑ q ∈ Icc 1 A, reducedLevelEnergy
      (fun q r => primeWindowResidueError q y h r) q) ≤
      (InnerFloorLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d ∈ Icc 1 A, primitivePrimeWindowEnergy d y h := by
  apply reducedFamilyEnergyLog
  · intro d
    exact sum_nonneg fun _ _ => sq_nonneg _
  · intro q inst hq d hd
    have hqy : (q : ℝ) ≤ y := (by exact_mod_cast hq : (q : ℝ) ≤ A).trans hy
    simp only [primeWindowCharacterError, InnerFloorAP.centeredPrimeSum_changeLevel hd _ hqy hh,
      primitivePrimeWindowEnergy, le_refl]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPrimitiveFamilyBridge.lean; sha256 738e1cd5a79c2cd3f5bfb922a80dff3823f5d9aa669c17e355aae5560c979b8d -/
section
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
      have he : (primitiveCharacters q).filter (fun χ => χ ≠ 1) =
          (primitiveCharacters q).erase 1 := by ext χ; simp [and_comm]
      rw [if_pos hq1,he]
      have hgP : g q (1:DirichletCharacter ℂ q) = P := by
        subst q
        rfl
      calc
        _ = (∑ χ∈(primitiveCharacters q).erase 1,g q χ)+g q 1 :=
          (sum_erase_add _ _ hmem).symm
        _ = _ := by rw [hgP]
      all_goals first | exact le_rfl | (apply le_of_eq; congr 1; apply sum_congr; · ext x; simp; · intros; rfl)
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

end

/-! BEGIN InnerFloorPrincipalWindow.lean; sha256 27dbb0571fc97283db7ad41c190ca6b5436d42d13f9ec98a5cc79a80c1cf3347 -/
section
/-!
Unconditional principal short-window estimate retaining logarithmic
saving rather than collapsing the bound to h/4. Adapted from the
accepted DyadicCellShortPrimeFloor, actual_principal_window_of_zero_weights,
pinned upstream 1fe24b28. No extra zero-free hypothesis.
-/
open Finset Filter
open scoped BigOperators Classical Topology
open OAI.Ostmann GoldbachOC103 Vx V7e V86 V1e V6i
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem principalWindowLogFour :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(4/5 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ C*(h : ℝ)/(Real.log X)^4 := by
  have hzero := actual_zero_weight_bounds
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets D C C hD.le
  obtain ⟨Xp,hXp⟩ := eventually_atTop.mp
    (eventually_power_log_bound (3/4) (4/5) 1 1 4 (by norm_num) (by norm_num))
  refine ⟨2*C+1,by positivity,max Xz (max Xb Xp),?_⟩
  intro X hX h hlower hupper
  have hbud := hb X ((le_max_left Xb Xp).trans ((le_max_right _ _).trans hX))
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X^(2/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X^(5/16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X ((le_max_left _ _).trans hX) hX4
    hbud.log_ge_one hbud.split_ge_two hbud.split_le_scale
  let S := V3b X
  let A := S.filter (fun c => |c.val.1.im| ≤ X^(5/16 : ℝ))
  let R := S.filter (fun c => ¬ |c.val.1.im| ≤ X^(5/16 : ℝ))
  let K := C*(Real.log X)^14/(X^(5/16 : ℝ)*Real.sqrt (X^(5/16 : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : ∀ c ∈ S, |c.val.1.im| ≤ X := by
    intro c hc
    exact (V5l X c).mp hc
  have hlow : (∑ c ∈ A, X^(c.val.1.re-1)) ≤ C/(Real.log X)^4 :=
    hlo A (fun c hc => (mem_filter.mp hc).2)
  have hhigh : ∀ v : ℝ, X^(5/16 : ℝ) ≤ v →
      (∑ c ∈ R.filter (fun c => |c.val.1.im| ≤ v), X^(c.val.1.re-1)) ≤
        K*v*Real.sqrt v := by
    intro v hv
    exact weight_count_clamp R X (X^(5/16 : ℝ)) K v hV hbud.split_le_scale hK hv
      (fun c hc => hS c (mem_filter.mp hc).1) hcount
  have hpacket := smoothed_packet_of_weight_bounds S (fun c => c.val.1)
    X X h (X^(2/3 : ℝ)) (X^(5/16 : ℝ)) (C/(Real.log X)^4) K
    (by linarith) le_rfl (by linarith) hh hupper hδ hbud.smoothing_le_half hV hK
    (fun c _ => c.property.1.1) (fun c _ => c.property.1.2.1.le) hlow hhigh
  have hHighBudget :
      576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
        X^(3/4 : ℝ)/16 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    exact hbud.high_budget
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ X^(3/4 : ℝ)/16 := by
    exact hres.trans hbud.residual_budget
  have hnorm : ‖V42 h X‖ ≤
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ +
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
        (V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
  have hsmall := (hXp X ((le_max_right Xb Xp).trans ((le_max_right _ _).trans hX))).2
  have hlogp : 0 < Real.log X := by linarith [hbud.log_ge_one]
  have hsmall' : X^(3/4 : ℝ) ≤ (h:ℝ)/(Real.log X)^4 := by
    apply (le_div_iff₀ (pow_pos hlogp 4)).2
    have hs : X^(3/4 : ℝ)*(Real.log X)^4 ≤ X^(4/5 : ℝ) := by
      simpa only [one_mul] using hsmall
    exact hs.trans hlower
  calc
    _ ≤ X^(3/4 : ℝ)/16 +
      (2*(h:ℝ)*(C/(Real.log X)^4)+X^(3/4 : ℝ)/16) :=
      hnorm.trans (add_le_add hResidualBudget (hpacket.trans
        (add_le_add_right hHighBudget _)))
    _ ≤ _ := by
      linarith only [hsmall',div_nonneg hh (pow_nonneg hlogp.le 4),
        show (2*C+1)*(h:ℝ)/(Real.log X)^4 =
          2*(h:ℝ)*(C/(Real.log X)^4)+(h:ℝ)/(Real.log X)^4 by ring]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPrincipalPrimeWindow.lean; sha256 fac11ade5d656d636f05f28b9ae22c21c091dfb6656ad7e502ba470d8908202d -/
section
/-! Principal prime window, without the nonprincipal zero-strip input. -/
open Finset Filter ArithmeticFunction
open scoped Classical Topology
open OAI.Ostmann V7e V2h GoldbachOC103
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem principalPrimePowerWindowError (χ : DirichletCharacter ℂ 1)
    {X y : ℝ} (h : ℕ) (hy : 0 ≤ y) (hX : y+(h:ℝ) ≤ X) :
    ‖V42 h y - InnerFloorAP.centeredPrimeSum χ y h‖ ≤
      Chebyshev.psi X-Chebyshev.theta X := by
  have hχ : χ=1 := by
    ext1 r
    rw [show r=1 from Subsingleton.elim _ _]
    simp
  subst χ
  let s := V9a h y
  have hsub : s ⊆ Ioc 0 ⌊X⌋₊ := by
    intro k hk
    have hm : k∈Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ := by
      simpa only [s,windowIndices_eq y h hy] using hk
    have hk' := (InnerFloorAP.mem_window hy (Nat.cast_nonneg h) k).mp hm
    exact mem_Ioc.mpr ⟨by exact_mod_cast hy.trans_lt hk'.1,
      (Nat.le_floor_iff (by linarith [Nat.cast_nonneg (α := ℝ) h])).2 (hk'.2.trans hX)⟩
  have he := weightedPrimePowerError s X hsub (fun _ => 1) (by simp)
  have hval (k : ℕ) : (1 : DirichletCharacter ℂ 1) (k:ZMod 1)=1 := by
    rw [show (k:ZMod 1)=1 from Subsingleton.elim _ _]
    simp
  unfold V42 InnerFloorAP.centeredPrimeSum
  rw [if_pos rfl,← windowIndices_eq y h hy]
  simp only [hval,mul_one,V1n]
  rw [show ((h:ℝ):ℂ)=(h:ℂ) by norm_cast, sub_sub_sub_cancel_right]
  simpa only [s,mul_one,logPrimeWeight] using he

theorem principalPrimeWindowLogFour :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(4/5:ℝ) ≤ (h:ℝ) → (h:ℝ) ≤ X → ∀ χ : DirichletCharacter ℂ 1,
      ‖InnerFloorAP.centeredPrimeSum χ X h‖ ≤ C*(h:ℝ)/(Real.log X)^4 := by
  obtain ⟨C,hC,X₁,h₁⟩ := principalWindowLogFour
  obtain ⟨X₂,h₂⟩ := eventually_atTop.mp
    (eventually_power_log_bound (1/2) (4/5) 8 1 5 (by norm_num) (by norm_num))
  refine ⟨C+1,by positivity,max 2 (max X₁ X₂),le_max_left ..,?_⟩
  intro X hX h hh hhX χ
  have hX2 : 2≤X := (le_max_left _ _).trans hX
  have hX1 : X₁≤X := (le_max_left X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hX₂ : X₂≤X := (le_max_right X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hXp : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog : Real.log (2*X) ≤ 2*Real.log X := by
    rw [Real.log_mul (by norm_num) hXp.ne']
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 2) hX2]
  have hsqrt : Real.sqrt (2*X) ≤ 2*Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2 ≤ 2) (Real.sqrt_nonneg _)
  have hpow := (h₂ X hX₂).2
  have hsmall : 8*Real.sqrt X*Real.log X ≤ (h:ℝ)/(Real.log X)^4 := by
    apply (le_div_iff₀ (pow_pos hL 4)).2
    calc
      _ = 8*X^(1/2:ℝ)*(Real.log X)^5 := by rw [Real.sqrt_eq_rpow]; ring
      _ ≤ _ := (by simpa only [one_mul] using hpow : 8*X^(1/2:ℝ)*(Real.log X)^5 ≤ X^(4/5:ℝ)).trans hh
  have herr := principalPrimePowerWindowError χ (X := 2*X) h hXp.le (by linarith)
  have herror : ‖V42 h X-InnerFloorAP.centeredPrimeSum χ X h‖ ≤ (h:ℝ)/(Real.log X)^4 := by
    apply herr.trans
    apply (Chebyshev.psi_sub_theta_le (by linarith : 1 ≤ 2*X)).trans
    calc
      _ ≤ 2*(2*Real.sqrt X)*(2*Real.log X) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        · exact hlog
        · exact Real.log_nonneg (by linarith)
        · positivity
      _ = 8*Real.sqrt X*Real.log X := by ring
      _ ≤ _ := hsmall
  have hnorm := norm_sub_le (V42 h X) (V42 h X-InnerFloorAP.centeredPrimeSum χ X h)
  rw [sub_sub_cancel] at hnorm
  calc
    _ ≤ _ := hnorm
    _ ≤ C*(h:ℝ)/(Real.log X)^4+(h:ℝ)/(Real.log X)^4 :=
      add_le_add (h₁ X hX1 h hh hhX) herror
    _ = _ := by ring

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorReducedGallagher.lean; sha256 c8ab1eb19cb343c545fe2dc706e54933e69ea9bd4d75727892e88888c0803b6e -/
section
/-!
Reduced-numerator Gallagher reduction. Unlike GBSkirtVariance.denominator_bound
this never sums over the nonunit numerators and never relaxes to q times the
full residue variance. The exact interior window is identified with the
verified conductor-lift estimate. The clipped endpoint windows are separate.
-/

open Finset MeasureTheory
open scoped Interval Classical
open GoldbachWindow (poly moving)
open GoldbachGRHAnalytic (errorCoeff)
open GoldbachGRHWindow (primeLog)
open Conjectures.Goldbach.ReflectionCharacterContraction_aux
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem reducedDenominatorBound {q : ℕ} [NeZero q] (n h : ℕ)
    (δ : ℝ) (hh : 0<h) (hd : 0≤δ) (hw : 6*(h:ℝ)*δ≤1) :
    (h:ℝ)^2/4 * (∑ a : (ZMod q)ˣ,
      ∫ t in -δ..δ, ‖poly (n+1) (errorCoeff (a:ZMod q)) t‖^2) ≤
      ∑ m∈range (n+1+h), ∑ a : (ZMod q)ˣ,
        ‖moving (n+1) h (errorCoeff (a:ZMod q)) m‖^2 := by
  rw [Finset.mul_sum,Finset.sum_comm (s := range (n+1+h))]
  exact sum_le_sum fun a _ =>
    GoldbachWindow.low_frequency_le (n+1) h (errorCoeff (a:ZMod q)) δ hh hd hw

theorem interiorWindowIndices (n y h : ℕ) (hfull : y+h≤n) :
    GBSkirtVariance.window n h (y+h) = Icc (y+1) (y+h) := by
  unfold GBSkirtVariance.window
  rw [min_eq_left hfull,show y+h+1-h=y+1 by omega]

theorem interiorResidueError_eq_zero {q : ℕ} [NeZero q]
    (n y h : ℕ) (hqy : q≤y) (hfull : y+h≤n)
    (r : ZMod q) (hr : ¬IsUnit r) :
    GBSkirtVariance.residueError (GBSkirtVariance.window n h (y+h)) primeLog r = 0 := by
  rw [interiorWindowIndices n y h hfull]
  unfold GBSkirtVariance.residueError
  rw [if_neg hr,sub_zero]
  change (∑ k ∈ (Icc (y+1) (y+h)).filter (fun k : ℕ => (k:ZMod q)=r),
    primeLog k)=0
  apply sum_eq_zero
  intro k hk
  obtain ⟨hk',hkr⟩ := mem_filter.mp hk
  have hqk : q<k := by have := (mem_Icc.mp hk').1; omega
  have hnp : ¬k.Prime := by
    intro hp
    have hcop : k.Coprime q := hp.coprime_iff_not_dvd.mpr
      (fun hd => (Nat.not_le_of_gt hqk) (Nat.le_of_dvd (NeZero.pos q) hd))
    exact hr (hkr ▸ (ZMod.isUnit_iff_coprime k q).mpr hcop)
  simp [primeLog,hnp]

theorem interiorResidueError_eq {q : ℕ} [NeZero q] (n y h : ℕ)
    (hfull : y+h≤n) (r : (ZMod q)ˣ) :
    GBSkirtVariance.residueError (GBSkirtVariance.window n h (y+h))
      primeLog (r:ZMod q) = primeWindowResidueError q y h r := by
  rw [interiorWindowIndices n y h hfull]
  unfold GBSkirtVariance.residueError
  change (∑ k ∈ (Icc (y+1) (y+h)).filter (fun k : ℕ => (k:ZMod q)=(r:ZMod q)),
    primeLog k) - (if IsUnit (r:ZMod q) then
      ((Icc (y+1) (y+h)).card:ℂ)/(q.totient:ℂ) else 0) =
    primeWindowResidueError q y h r
  simp only [r.isUnit,if_pos,primeWindowResidueError,dif_neg (NeZero.ne q),
    InnerFloorAP.theta,← Nat.cast_add,Nat.floor_natCast,Complex.ofReal_sum,
    Complex.ofReal_div,Complex.ofReal_natCast,primeLog]
  congr 1
  have hc : (Icc (y+1) (y+h)).card=h := by rw [Nat.card_Icc]; omega
  rw [hc]

theorem interiorMoving_eq_reduced {q : ℕ} [NeZero q] (n y h : ℕ)
    (hqy : q≤y) (hfull : y+h≤n) (a : (ZMod q)ˣ) :
    moving (n+1) h (errorCoeff (a:ZMod q)) (y+h) =
      unitAdditiveError (primeWindowResidueError q y h) a := by
  rw [GBSkirtVariance.moving_fourier]
  unfold unitAdditiveError
  rw [← sum_units_eq_sum
    (fun r : ZMod q => GBSkirtVariance.residueError
      (GBSkirtVariance.window n h (y+h)) primeLog r *
      ZMod.stdAddChar ((a:ZMod q)*r))
    (fun r hr => by rw [interiorResidueError_eq_zero n y h hqy hfull r hr,zero_mul])]
  exact sum_congr rfl fun r _ => by rw [interiorResidueError_eq n y h hfull]

def reducedMovingLevelEnergy (q n h m : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : (ZMod q)ˣ, ‖moving (n+1) h (errorCoeff (a:ZMod q)) m‖^2

/-- Full interior windows over any bounded family of levels satisfy the
same logarithmic conductor-lifting bound. No additional q factor. -/
theorem interiorReducedMovingFamilyEnergy (A n y h : ℕ)
    (hAy : A≤y) (hfull : y+h≤n) :
    (∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h (y+h)) ≤
      (InnerFloorLinearTotient.weightConstant*(1+Real.log A))^2 *
        ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h := by
  calc
    _ = ∑ q∈Icc 1 A, reducedLevelEnergy
      (fun q r => primeWindowResidueError q y h r) q := by
      apply sum_congr rfl
      intro q hq
      have hq0 : q≠0 := by have := (mem_Icc.mp hq).1; omega
      letI : NeZero q := ⟨hq0⟩
      simp only [reducedMovingLevelEnergy,reducedLevelEnergy,dif_neg hq0]
      apply sum_congr rfl
      intro a _
      rw [interiorMoving_eq_reduced n y h ((mem_Icc.mp hq).2.trans hAy) hfull]
    _ ≤ _ := primeWindowReducedFamilyEnergy A y h
      (by exact_mod_cast hAy) (Nat.cast_nonneg h)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorDiscreteWindowEnergy.lean; sha256 50d3e37cefa18b2d53b7a302c5618238db4e07ff9bfe8f8e9849801575f47197 -/
section
/-!
Integer-to-real window energy without any inequality loss.
Generic step integral adapted from GBSkirtVariance.paper_integral,
accepted LowSkirtFromShortProgressions at pinned upstream 1fe24b28.
-/
open Finset MeasureTheory
open scoped Classical Interval
namespace InnerFloorResearch
noncomputable section

theorem centeredPrimeSum_on_unit {d : ℕ}
    (χ : DirichletCharacter ℂ d) (k h : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ico (k:ℝ) ((k+1:ℕ):ℝ)) :
    InnerFloorAP.centeredPrimeSum χ y h =
      InnerFloorAP.centeredPrimeSum χ (k:ℝ) h := by
  have hy₀ := (Nat.cast_nonneg k (α:=ℝ)).trans hy.1
  have hk : ⌊y⌋₊=k := (Nat.floor_eq_iff hy₀).2 ⟨hy.1,by simpa using hy.2⟩
  simp only [InnerFloorAP.centeredPrimeSum,Nat.floor_add_natCast hy₀,
    hk,Nat.floor_natCast,Nat.floor_add_natCast (Nat.cast_nonneg (α:=ℝ) k)]

theorem primitivePrimeWindowEnergy_on_unit (d k h : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ico (k:ℝ) ((k+1:ℕ):ℝ)) :
    primitivePrimeWindowEnergy d y h = primitivePrimeWindowEnergy d k h := by
  unfold primitivePrimeWindowEnergy
  apply sum_congr rfl
  intro χ _
  rw [centeredPrimeSum_on_unit χ k h hy]

theorem integer_step_integral (x z : ℕ) (hxz : x≤z)
    (f : ℝ → ℝ) (g : ℕ → ℝ)
    (hstep : ∀ k : ℕ, ∀ y∈Set.Ico (k:ℝ) ((k+1:ℕ):ℝ), f y=g k) :
    (∫ y in (x:ℝ)..(z:ℝ), f y) = ∑ k∈Ico x z,g k := by
  let a (k : ℕ) := (k:ℝ)
  have hle (k : ℕ) : a k ≤ a (k+1) := by dsimp [a]; push_cast; linarith
  have hi (k : ℕ) : IntervalIntegrable f volume (a k) (a (k+1)) := by
    apply (intervalIntegrable_iff_integrableOn_Ico_of_le (hle k)).2
    have hc : IntegrableOn (fun _ : ℝ => g k) (Set.Ico (a k) (a (k+1))) volume :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le (hle k)).1 intervalIntegrable_const
    apply hc.congr_fun _ measurableSet_Ico
    intro y hy
    exact (hstep k y hy).symm
  have he (k : ℕ) : (∫ y in a k..a (k+1), f y) = g k := by
    rw [intervalIntegral.integral_of_le (hle k), ← integral_Ico_eq_integral_Ioc]
    calc
      _ = ∫ _y in Set.Ico (a k) (a (k+1)), g k := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro y hy
        exact hstep k y hy
      _ = _ := by simp [a,Real.volume_Ico]
  have ht := intervalIntegral.sum_integral_adjacent_intervals_Ico (a:=a) (m:=x) (n:=z)
    hxz (fun k _ => hi k)
  exact ht.symm.trans (sum_congr rfl fun k _ => he k)

theorem primitiveFamilyIntegerEnergy (A h x z : ℕ) (hxz : x≤z) :
    (∑ k∈Ico x z, ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d k h) =
      ∫ y in (x:ℝ)..(z:ℝ), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h := by
  symm
  apply integer_step_integral x z hxz
  intro k y hy
  exact sum_congr rfl fun d _ => primitivePrimeWindowEnergy_on_unit d k h hy

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorGoodZeroWindow.lean; sha256 04947e34415b17372c0c133c87734bab40ed9812a6908529513fca7a6862e34a -/
section
/-!
Research auxiliary: the accepted primitive-character zero-density mean-square
estimate applies to the entire fixed-strip part of the zero spectrum on the
inner-arc window scale. This does NOT assert that the remaining zero spectrum
is empty, and does NOT assume or import GRH.
-/

open Finset Filter MeasureTheory
open scoped Interval Topology Classical
open OAI.Ostmann V1l V1e Vg2
namespace InnerFloorResearch
noncomputable section

/-- A fixed strip gap eventually dominates the logarithmic cutoff of the
existing zero-density estimate. -/
theorem fixedStripDominatesCutoff (B : ℕ) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, V2j (B+4) X ≤ (1/8 : ℝ) := by
  have ht : Tendsto (fun X : ℝ => Real.log (Real.log X)/Real.log X)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have h := (tendsto_const_nhds (x := (3 : ℝ)*((B+4+14 : ℕ) : ℝ))).mul ht
  have he := h.eventually (gt_mem_nhds (show
    (3 : ℝ)*((B+4+14 : ℕ) : ℝ)*0 < 1/8 by norm_num))
  have he' : ∀ᶠ X : ℝ in atTop, V2j (B+4) X ≤ (1/8 : ℝ) := by
    filter_upwards [he] with X hX
    have hX' : (3 : ℝ)*((B+4+14 : ℕ) : ℝ)*
        (Real.log (Real.log X)/Real.log X) < 1/8 := by simpa using hX
    unfold V2j
    rw [mul_div_assoc]
    exact hX'.le
  exact eventually_atTop.mp he'

/-- For the dyadic height band, the entire 1/2 <= beta <= 7/8 component
has a log-saving mean square. The family and zero subsets can vary freely. -/
theorem fixedStripWindowBand (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h T : ℝ,
      X₀≤X → 2≤T → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ ⊆ ((V1 χ).V14 T).filter (fun i =>
        1/2≤((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re≤7/8 ∧
        T/2≤|((V1 χ).zeros i).im|)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,h₁⟩ := V93.Vz7 B
  obtain ⟨X₂,h₂⟩ := fixedStripDominatesCutoff B
  refine ⟨C,hC,max X₁ X₂,?_⟩
  intro Q hQ X h T hX hT hh hhX hscale hlog F hF S hS
  apply h₁ Q hQ X h T ((le_max_left _ _).trans hX) hT hh hhX
    hscale hlog F hF S
  intro χ hχ i hi
  obtain ⟨hiT,hiR,hiB,hiH⟩ := mem_filter.mp (hS χ hχ hi)
  have hc := h₂ X ((le_max_right _ _).trans hX)
  unfold Vy2
  exact mem_filter.mpr ⟨hiT,hiR,by linarith,hiH⟩

/-- At height <= 2, the same estimate holds, without a lower-height
restriction. -/
theorem fixedStripWindowLow (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h : ℝ,
      X₀≤X → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*2)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ ⊆ ((V1 χ).V14 2).filter (fun i =>
        1/2≤((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re≤7/8)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,h₁⟩ := V93.V1ep B
  obtain ⟨X₂,h₂⟩ := fixedStripDominatesCutoff B
  refine ⟨C,hC,max X₁ X₂,?_⟩
  intro Q hQ X h hX hh hhX hscale hlog F hF S hS
  apply h₁ Q hQ X h ((le_max_left _ _).trans hX) hh hhX
    hscale hlog F hF S
  intro χ hχ i hi
  obtain ⟨hiT,hiR,hiB⟩ := mem_filter.mp (hS χ hχ hi)
  have hc := h₂ X ((le_max_right _ _).trans hX)
  exact mem_filter.mpr ⟨hiT,hiR,by linarith⟩

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorGoodZeroAssembly.lean; sha256 c28ec698a44d44c1795cfcd12d1159b20b3c9dab91199d50100716aa63543ded -/
section
/-!
All-height, fixed-strip primitive-character window energy.
The near-one zeros are deliberately not discarded: the conclusions apply
to arbitrary subsets satisfying the stated real-part cutoff.
-/

open Finset Filter MeasureTheory
open scoped Interval Topology Classical
open OAI.Ostmann V1e V6b V6i
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def zeroWindow (χ : PrimitiveComplexCharacter) (S : Finset ℕ)
    (h y : ℝ) : ℂ :=
  ∑ i ∈ S, Ve y h ((V1 χ).zeros i)

/-- Sum all the dyadic bands in the strip 1/2 ≤ Re ρ ≤ 7/8.
The loss is at most (K+1)^2, for U=2^(K+1). -/
theorem rightStripAllHeights (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ),
      1 ≤ Q → X₀ ≤ X → 0 < h → h ≤ X →
      (Q : ℝ)^2/(h/X) ≤ X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1)) ≤ 2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ ∈ F, S χ ⊆ (V1 χ).V14 ((2 : ℝ)^(K+1))) →
      (∀ χ ∈ F, ∀ i ∈ S χ, 1/2 ≤ ((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re ≤ 7/8) →
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        C*((K+1 : ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := fixedStripWindowBand B
  obtain ⟨C₂,hC₂,X₂,h₂⟩ := fixedStripWindowLow B
  let C := max C₁ C₂
  refine ⟨C, hC₁.trans_le (le_max_left ..), max (max X₁ X₂) 2,
    by linarith [le_max_right (max X₁ X₂) (2:ℝ)], ?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF S hS hstrip
  have hX1 := (le_max_left X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hX2 := (le_max_right X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hXp : 0 < X := by linarith [(le_max_right (max X₁ X₂) (2:ℝ)).trans hX]
  have hXge : 2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  let P (k : ℕ) (χ : PrimitiveComplexCharacter) :=
    Vpt (S χ) (fun i => ((V1 χ).zeros i).im) k
  have hpart (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (y : ℝ) :
      zeroWindow χ (S χ) h y =
        ∑ k ∈ range (K+1), zeroWindow χ (P k χ) h y := by
    unfold zeroWindow
    apply V9u
    intro i hi
    exact (ComplexZeroEnumeration.V2r _ _ _).mp (hS χ hχ hi)
  have hpow (k : ℕ) (hk : k ∈ range (K+1)) :
      (2 : ℝ)^(k+1) ≤ 2^(K+1) :=
    pow_le_pow_right₀ (by norm_num) (by have := mem_range.mp hk; omega)
  have hT (k : ℕ) : (2 : ℝ) ≤ 2^(k+1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ k+1 by omega))
  have hlogk (k : ℕ) (hk : k ∈ range (K+1)) :
      Real.log ((Q : ℝ)*2^(k+1)) ≤ 2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (hpow k hk) (Nat.cast_nonneg _)
  have hblock (k : ℕ) (hk : k ∈ range (K+1)) :
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
    by_cases hk0 : k = 0
    · subst k
      have h := h₂ Q hQ X h hX2 hh hhX hscale
        (by simpa using hlogk 0 hk) F hF (P 0)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,_⟩ := mem_filter.mp hi
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr
            (by simpa using hiT),hstrip χ hχ i hiS⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_right ..)
    · have h := h₁ Q hQ X h ((2:ℝ)^(k+1)) hX1 (hT k) hh hhX hscale
        (hlogk k hk) F hF (P k)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,hiL⟩ := mem_filter.mp hi
          have hL' := hiL.resolve_left hk0
          have he : (2:ℝ)^(k+1)/2 = 2^k := by rw [pow_succ]; ring
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr hiT,
            (hstrip χ hχ i hiS).1,(hstrip χ hχ i hiS).2,by rw [he]; exact hL'.le⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_left ..)
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      (∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
    simp_rw [hpart χ hχ]
    simpa only [card_range] using
      (V1dr (range (K+1)) (fun k y => zeroWindow χ (P k χ) h y) X hXp.le
        (fun k _ => ContinuousOn.intervalIntegrable_of_Icc (by linarith)
          ((V6e (P k χ) (V1 χ).zeros X h hXp hh.le hhX).norm.pow 2)))
  calc
    _ ≤ ∑ χ ∈ F, ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) :=
      sum_le_sum hterm
    _ = ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1), ∑ χ ∈ F,
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
      rw [← mul_sum, sum_comm]
    _ ≤ ((K+1 : ℕ):ℝ)*(∑ _k ∈ range (K+1), C*h^2*X/(Real.log X)^B) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hblock) (by positivity)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- Sum all the dyadic bands in the strip 1/2 ≤ Re ρ ≤ 1 - V2j (B+4) X.
The loss is at most (K+1)^2, for U=2^(K+1). -/
theorem goodZerosAllHeights (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ),
      1 ≤ Q → X₀ ≤ X → 0 < h → h ≤ X →
      (Q : ℝ)^2/(h/X) ≤ X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1)) ≤ 2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ ∈ F, S χ ⊆ (V1 χ).V14 ((2 : ℝ)^(K+1))) →
      (∀ χ ∈ F, ∀ i ∈ S χ, 1/2 ≤ ((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re ≤ 1 - V1l.V2j (B+4) X) →
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        C*((K+1 : ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := V93.Vz7 B
  obtain ⟨C₂,hC₂,X₂,h₂⟩ := V93.V1ep B
  let C := max C₁ C₂
  refine ⟨C, hC₁.trans_le (le_max_left ..), max (max X₁ X₂) 2,
    by linarith [le_max_right (max X₁ X₂) (2:ℝ)], ?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF S hS hstrip
  have hX1 := (le_max_left X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hX2 := (le_max_right X₁ X₂).trans ((le_max_left _ _).trans hX)
  have hXp : 0 < X := by linarith [(le_max_right (max X₁ X₂) (2:ℝ)).trans hX]
  have hXge : 2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  let P (k : ℕ) (χ : PrimitiveComplexCharacter) :=
    Vpt (S χ) (fun i => ((V1 χ).zeros i).im) k
  have hpart (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) (y : ℝ) :
      zeroWindow χ (S χ) h y =
        ∑ k ∈ range (K+1), zeroWindow χ (P k χ) h y := by
    unfold zeroWindow
    apply V9u
    intro i hi
    exact (ComplexZeroEnumeration.V2r _ _ _).mp (hS χ hχ hi)
  have hpow (k : ℕ) (hk : k ∈ range (K+1)) :
      (2 : ℝ)^(k+1) ≤ 2^(K+1) :=
    pow_le_pow_right₀ (by norm_num) (by have := mem_range.mp hk; omega)
  have hT (k : ℕ) : (2 : ℝ) ≤ 2^(k+1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ k+1 by omega))
  have hlogk (k : ℕ) (hk : k ∈ range (K+1)) :
      Real.log ((Q : ℝ)*2^(k+1)) ≤ 2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (hpow k hk) (Nat.cast_nonneg _)
  have hblock (k : ℕ) (hk : k ∈ range (K+1)) :
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
    by_cases hk0 : k = 0
    · subst k
      have h := h₂ Q hQ X h hX2 hh hhX hscale
        (by simpa using hlogk 0 hk) F hF (P 0)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,_⟩ := mem_filter.mp hi
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr
            (by simpa using hiT),hstrip χ hχ i hiS⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_right ..)
    · have h := h₁ Q hQ X h ((2:ℝ)^(k+1)) hX1 (hT k) hh hhX hscale
        (hlogk k hk) F hF (P k)
        (by
          intro χ hχ i hi
          obtain ⟨hiS,hiT,hiL⟩ := mem_filter.mp hi
          have hL' := hiL.resolve_left hk0
          have he : (2:ℝ)^(k+1)/2 = 2^k := by rw [pow_succ]; ring
          exact mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r _ _ _).mpr hiT,
            (hstrip χ hχ i hiS).1,(hstrip χ hχ i hiS).2,by rw [he]; exact hL'.le⟩)
      exact h.trans (by dsimp [C]; gcongr; exact le_max_left ..)
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ ∈ F) :
      (∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) ≤
        ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
    simp_rw [hpart χ hχ]
    simpa only [card_range] using
      (V1dr (range (K+1)) (fun k y => zeroWindow χ (P k χ) h y) X hXp.le
        (fun k _ => ContinuousOn.intervalIntegrable_of_Icc (by linarith)
          ((V6e (P k χ) (V1 χ).zeros X h hXp hh.le hhX).norm.pow 2)))
  calc
    _ ≤ ∑ χ ∈ F, ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1),
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) :=
      sum_le_sum hterm
    _ = ((K+1 : ℕ):ℝ)*(∑ k ∈ range (K+1), ∑ χ ∈ F,
          ∫ y in X..2*X, ‖zeroWindow χ (P k χ) h y‖^2) := by
      rw [← mul_sum, sum_comm]
    _ ≤ ((K+1 : ℕ):ℝ)*(∑ _k ∈ range (K+1), C*h^2*X/(Real.log X)^B) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hblock) (by positivity)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- Moving-average smoothing does not increase energy beyond the
slightly enlarged physical interval. -/
theorem smoothedWindowEnergy
    (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {X h δ : ℝ}
    (hX : 0 < X) (hh : 0 ≤ h) (hhX : h ≤ X/2)
    (hδ : 0 < δ) (hδX : δ ≤ X/2) :
    (∑ χ ∈ F, ∫ y in X..2*X, ‖V3q (zeroWindow χ (S χ) h) δ y‖^2) ≤
      (∑ χ ∈ F, ∫ y in X/2..X, ‖zeroWindow χ (S χ) h y‖^2) +
      (∑ χ ∈ F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2) := by
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro χ _
  let f := zeroWindow χ (S χ) h
  have hcont : ContinuousOn f (Set.Icc (X/2) (2*X)) := by
    unfold f zeroWindow
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hpos : y+h ≠ 0 := by linarith [hy.1]
      have hc : ContinuousAt (fun t : ℝ => t+h) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t : ℝ => ((t+h:ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+h) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+h) ((V1 χ).zeros i) (Or.inr hpos)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y ≠ 0))).continuousWithinAt
  have hsub : Set.Icc (X-δ) (2*X) ⊆ Set.Icc (X/2) (2*X) :=
    Set.Icc_subset_Icc (by linarith) le_rfl
  apply (V1qh f X δ hX.le hδ (hcont.mono hsub)).trans
  have hint : IntervalIntegrable (fun y => ‖f y‖^2) volume (X/2) (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hcont.norm.pow 2)
  calc
    _ ≤ ∫ u in X/2..2*X, ‖f u‖^2 :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith)
        le_rfl (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hint
    _ = _ := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hint.mono_set (by rw [Set.uIcc_of_le (by linarith : X/2≤X),
          Set.uIcc_of_le (by linarith : X/2≤2*X)]; exact Set.Icc_subset_Icc le_rfl (by linarith)))
        (hint.mono_set (by rw [Set.uIcc_of_le (by linarith : X≤2*X),
          Set.uIcc_of_le (by linarith : X/2≤2*X)]; exact Set.Icc_subset_Icc (by linarith) le_rfl))]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPolynomialWindow.lean; sha256 7f4a3a9e90a224457177cafec7417d3f44893c102cdb2a156ec99283481e5fff -/
section
/-!
Adaptation of Vbt.V1mq, V86.Vja, V86.V10t from the accepted
DyadicCellShortPrimeFloor proof (LogTruSoul, PR #3746).
Only the modulus range is changed: Q ≤ X implies log q ≤ log X.
All explicit-formula ingredients are reused, not assumed.
-/

noncomputable section
open Complex Finset MeasureTheory
open scoped Interval BigOperators Classical
open OAI.Ostmann V82 V6i V1e Vx Vex Vbt V7e V86
namespace InnerFloorResearch.PolynomialWindow
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem sqrtLogPolynomial (X q Q u : ℝ)
    (hX : 4≤X) (hq : 1≤q) (hqQ : q≤Q) (hQX : Q≤X)
    (hu : 1≤u) (huX : u≤3*X) :
    Real.sqrt u*(1+Real.log q)≤52*Real.sqrt X*Real.log X := by
  have hXp : 0<X := by linarith
  have hqp : 0<q := by linarith
  have hLp : 0<Real.log X := Real.log_pos (by linarith)
  have hL : 1≤Real.log X := by
    apply (Real.le_log_iff_exp_le hXp).2
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hqlog : Real.log q≤Real.log X := Real.log_le_log hqp (hqQ.trans hQX)
  have hfactor : 1+Real.log q≤26*Real.log X := by linarith
  have hfactor0 : 0≤1+Real.log q := by linarith [Real.log_nonneg hq]
  have hsqrt : Real.sqrt u≤2*Real.sqrt X := by
    calc
      _ ≤ Real.sqrt (4*X) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hm := mul_le_mul hsqrt hfactor hfactor0 (by positivity)
  exact hm.trans_eq (by ring)

theorem smoothedRemainderPolynomial (f : ℝ → ℂ) (E q Q X y h δ : ℝ)
    (hE : 0≤E) (hq : 1≤q) (hqQ : q≤Q) (hQX : Q≤X)
    (hX : 4≤X) (hy : y∈Set.Icc X (2*X)) (hh : 0≤h) (hhX : h≤X)
    (hδ : 0<δ) (hδX : δ≤X/2)
    (hf : ∀ u:ℝ,1≤u → ‖f u‖≤E*Real.sqrt u*(1+Real.log q)) :
    ‖V1c f y h δ‖≤208*E*(Real.sqrt X*Real.log X/δ) := by
  have hb (u : ℝ) (hu : X/2≤u) (huX : u≤3*X) :
      ‖f u‖≤52*E*Real.sqrt X*Real.log X := by
    have hu1 : 1≤u := by linarith
    calc
      _ ≤ E*Real.sqrt u*(1+Real.log q) := hf u hu1
      _ = E*(Real.sqrt u*(1+Real.log q)) := by ring
      _ ≤ E*(52*Real.sqrt X*Real.log X) := mul_le_mul_of_nonneg_left
        (sqrtLogPolynomial X q Q u hX hq hqQ hQX hu1 huX) hE
      _ = _ := by ring
  have he := Vun f y h δ (52*E*Real.sqrt X*Real.log X) hδ
    (hb (y+h) (by linarith [hy.1]) (by linarith [hy.2]))
    (hb (y+h-δ) (by linarith [hy.1]) (by linarith [hy.2]))
    (hb y (by linarith [hy.1]) (by linarith [hy.2]))
    (hb (y-δ) (by linarith [hy.1]) (by linarith [hy.2]))
  exact he.trans_eq (by ring)

theorem nonprincipalWindowFormulaPolynomial :
    ∃ D:ℝ,0<D ∧ ∀ Q:ℕ,1≤Q → ∀ (X y δ U:ℝ) (h:ℕ),
      4≤X → y∈Set.Icc X (2*X) → (h:ℝ)≤X → 1≤δ → δ≤X/2 → 2≤U →
      (Q:ℝ)≤X →
      ∀ χ:PrimitiveComplexCharacter,χ.modulus≤Q →
      ‖V4q χ h y+
        V3q (fun u=>∑ i∈(V1 χ).V14 U,
          Ve u (h:ℝ) ((V1 χ).zeros i)) δ y‖≤
        D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
          (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
  obtain ⟨E,hE,hbound⟩ := Vt5
  have hT := Vj5
  refine ⟨20+208*E+V38,by positivity,?_⟩
  intro Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ hχ
  have hX2 : 2≤X := by linarith
  have hδp : 0<δ := by linarith
  have hyδ : δ<y := by linarith [hy.1]
  have hh : (0:ℝ)≤h := Nat.cast_nonneg h
  have hq : 1≤(χ.modulus:ℝ) := by exact_mod_cast χ.positive
  have hqQ : (χ.modulus:ℝ)≤Q := by exact_mod_cast hχ
  have hQr : 1≤(Q:ℝ) := by exact_mod_cast hQ
  have hlogX : 0≤Real.log X := Real.log_nonneg (by linarith)
  have hlogU : 0≤Real.log ((Q:ℝ)*U) := Real.log_nonneg (by nlinarith)
  obtain ⟨c,hc⟩ := hbound χ
  have huns := V1co χ h X y δ hX2 hy hhX hδ hδX
  have hrem := smoothedRemainderPolynomial (V7p χ c)
    E χ.modulus Q X y h δ hE.le hq hqQ hQX hX hy hh hhX hδp hδX hc
  have hori := V1wr χ X y h δ hX2 hy hh hhX hδ hδX
  have htail := V1t6 Q hQ χ hχ X y h δ U hX2 hy hh hhX hδp hδX hU
  have hid := V172 χ c y h δ U hδp hyδ hh
  have hn := V1gu (V4q χ h y) _ _ _ _ _ hid
  have hs : ‖V4q χ h y+
      V3q (fun u=>∑ i∈(V1 χ).V14 U,
        Ve u (h:ℝ) ((V1 χ).zeros i)) δ y‖≤
      18*(δ*Real.log X)+(208*E)*(Real.sqrt X*Real.log X/δ)+
        V38*((Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) := by
    linarith
  exact hs.trans (Vwl E (δ*Real.log X) (Real.sqrt X*Real.log X/δ)
    ((Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) hE (by positivity) (by positivity) (by positivity))

end InnerFloorResearch.PolynomialWindow
end

end

/-! BEGIN InnerFloorWindowFormulaEnergy.lean; sha256 87cda253583e6579a54e14ded217a941103080803f5596c58315a528e8ec150e -/
section
/-!
Local energy transfer from the polynomial-modulus explicit formula.
The residual is kept explicit; no zero-free hypothesis is used.
This connects the analytic formula to an actual arithmetic-window L² bound.
-/

open Finset MeasureTheory
open scoped Interval Classical
open OAI.Ostmann V1e V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem windowFormulaEnergy (g f : ℝ → ℂ) {X δ E : ℝ}
    (hX : 0 ≤ X) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hf : ContinuousOn f (Set.Icc (X-δ) (2*X)))
    (hres : ∀ y ∈ Set.Icc X (2*X), ‖g y + V3q f δ y‖ ≤ E) :
    (∫ y in X..2*X, ‖g y‖^2) ≤
      2*X*E^2 + 2*(∫ y in X-δ..2*X, ‖f y‖^2) := by
  have hXX : X ≤ 2*X := by linarith
  obtain ⟨hQ,hFubini⟩ := V16e (fun u => ‖f u‖^2) X δ hX hδ.le
    (hf.norm.pow 2) (fun _ _ => sq_nonneg _)
  have hp : ∀ y ∈ Set.Icc X (2*X),
      ‖g y‖^2 ≤ 2*E^2 + (2/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
    intro y hy
    have hc : ContinuousOn f (Set.Icc (y-δ) y) := hf.mono (by
      intro u hu
      exact ⟨by linarith [hy.1,hu.1],by linarith [hy.2,hu.2]⟩)
    have hs := Vl2.V1gz f (y-δ) y (by linarith) hc
    have hn : ‖V3q f δ y‖^2 ≤ (1/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
      have he : ‖V3q f δ y‖^2 =
          (δ⁻¹)^2*‖∫ u in y-δ..y,f u‖^2 := by
        rw [V3q,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hδ.le,mul_pow]
      rw [he]
      apply (mul_le_mul_of_nonneg_left hs (sq_nonneg (δ⁻¹))).trans_eq
      field_simp
      <;> ring
    have hnorm : ‖g y‖ ≤ E + ‖V3q f δ y‖ := by
      have h := norm_sub_le (g y + V3q f δ y) (V3q f δ y)
      rw [add_sub_cancel_right] at h
      linarith [hres y hy]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hs' : (E + ‖V3q f δ y‖)^2 ≤ 2*E^2+2*‖V3q f δ y‖^2 := by
      nlinarith [sq_nonneg (E-‖V3q f δ y‖)]
    refine hsq.trans (hs'.trans ?_)
    calc
      _ ≤ 2*E^2+2*((1/δ)*(∫ u in y-δ..y, ‖f u‖^2)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤2)) _
      _ = _ := by ring
  have hi : (∫ y in X..2*X, ‖g y‖^2) ≤
      ∫ y in X..2*X, 2*E^2 + (2/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
    rw [intervalIntegral.integral_of_le hXX,intervalIntegral.integral_of_le hXX]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (intervalIntegrable_const.add (hQ.const_mul (2/δ))).1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact hp y ⟨hy.1.le,hy.2⟩
  rw [intervalIntegral.integral_add intervalIntegrable_const (hQ.const_mul (2/δ)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul] at hi
  calc
    _ ≤ (2*X-X)*(2*E^2)+(2/δ)*(∫ y in X..2*X,∫ u in y-δ..y,‖f u‖^2) := hi
    _ ≤ (2*X-X)*(2*E^2)+(2/δ)*(δ*(∫ u in X-δ..2*X,‖f u‖^2)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hFubini (by positivity : 0≤(2:ℝ)/δ)) _
    _ = _ := by field_simp; ring

/-- The actual nonprincipal von Mangoldt short-window family is bounded by
the explicit formula residual plus the full zero-window energy. -/
theorem primitiveWindowEnergyFromZeros :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (X δ U : ℝ) (h : ℕ), 4 ≤ X → (h:ℝ) ≤ X →
      1 ≤ δ → δ ≤ X/2 → 2 ≤ U → (Q:ℝ) ≤ X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))
      (∑ χ∈F, ∫ y in X..2*X, ‖V4q χ h y‖^2) ≤
        2*X*(Q:ℝ)^2*E^2 +
          2*(∑ χ∈F, ∫ y in X-δ..2*X,
            ‖∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)‖^2) := by
  obtain ⟨D,hD,hformula⟩ := PolynomialWindow.nonprincipalWindowFormulaPolynomial
  refine ⟨D,hD,?_⟩
  intro Q hQ X δ U h hX hhX hδ hδX hU hQX F hF
  dsimp only
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))
  let f (χ : PrimitiveComplexCharacter) (y : ℝ) :=
    ∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)
  have hE : 0 ≤ E := by
    have hL : 0≤Real.log X := Real.log_nonneg (by linarith)
    have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
    have hL2 : 0≤Real.log ((Q:ℝ)*U) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQr (by linarith))
    dsimp [E]
    positivity
  have hcont (χ : PrimitiveComplexCharacter) :
      ContinuousOn (f χ) (Set.Icc (X-δ) (2*X)) := by
    unfold f
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hp : y+(h:ℝ) ≠ 0 := by linarith [hy.1, Nat.cast_nonneg (α := ℝ) h]
      have hc : ContinuousAt (fun t:ℝ => t+(h:ℝ)) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t : ℝ => ((t+(h:ℝ):ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+(h:ℝ)) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+(h:ℝ)) ((V1 χ).zeros i) (Or.inr hp)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y≠0))).continuousWithinAt
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ∈F) :
      (∫ y in X..2*X, ‖V4q χ h y‖^2) ≤
        2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2) :=
    windowFormulaEnergy (V4q χ h) (f χ) (by linarith) (by linarith) hE
      (hcont χ) (fun y hy =>
        hformula Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ (hF χ hχ))
  have hcard : (F.card:ℝ)≤(Q:ℝ)^2 := by exact_mod_cast V14i F Q hF
  change _ ≤ 2*X*(Q:ℝ)^2*E^2 + 2*(∑ χ∈F, ∫ y in X-δ..2*X,‖f χ y‖^2)
  calc
    _ ≤ ∑ χ∈F, (2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2)) :=
      sum_le_sum hterm
    _ = (F.card:ℝ)*(2*X*E^2)+2*(∑ χ∈F,∫ y in X-δ..2*X,‖f χ y‖^2) := by
      rw [sum_add_distrib,← mul_sum]
      simp only [sum_const,nsmul_eq_mul]
      rw [← mul_sum]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hcard (by positivity : 0≤2*X*E^2)
      linarith

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorFullSpectrum.lean; sha256 7500843247d0a2ec7e25d286557ef631dc7673d29fffe5e2d350ae909790ad45 -/
section
/-!
Full-spectrum energy with an explicitly retained near-one term.
No fixed zero-free strip is assumed or asserted.
-/
open Finset MeasureTheory Filter
open scoped Classical Interval Topology
open OAI.Ostmann V1e V6b V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def leftIndices (χ : PrimitiveComplexCharacter) (U : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => ((V1 χ).zeros i).re ≤ (2:ℝ)⁻¹

def rightGoodIndices (χ : PrimitiveComplexCharacter) (U c : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => (2:ℝ)⁻¹ < ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ c

def rightBadIndices (χ : PrimitiveComplexCharacter) (U c : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => (2:ℝ)⁻¹ < ((V1 χ).zeros i).re ∧ c < ((V1 χ).zeros i).re

theorem zeroWindow_partition (χ : PrimitiveComplexCharacter) (U c h y : ℝ) :
    zeroWindow χ ((V1 χ).V14 U) h y =
      zeroWindow χ (leftIndices χ U) h y +
      zeroWindow χ (rightGoodIndices χ U c) h y +
      zeroWindow χ (rightBadIndices χ U c) h y := by
  classical
  unfold zeroWindow leftIndices rightGoodIndices rightBadIndices
  simp only [sum_filter]
  rw [← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hl : ((V1 χ).zeros i).re ≤ (2:ℝ)⁻¹
  · simp [hl,not_lt_of_ge hl]
  · have hr := lt_of_not_ge hl
    by_cases hg : ((V1 χ).zeros i).re ≤ c
    · simp [hl,hr,hg,not_lt_of_ge hg]
    · simp [hl,hr,hg,lt_of_not_ge hg]

def zeroFamilyEnergy (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) (X h : ℝ) : ℝ :=
  ∑ χ∈F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2

theorem zeroFamilyEnergy_nonneg (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {X h : ℝ} (hX : 0≤X) :
    0≤zeroFamilyEnergy F S X h :=
  sum_nonneg fun _ _ => intervalIntegral.integral_nonneg_of_forall (by linarith)
    fun _ => sq_nonneg _

/-- Only the last, near-one spectral term is uncontrolled. The
factor 3 follows from finite Cauchy--Schwarz rather than cancellation. -/
theorem fullSpectrumSplit (F : Finset PrimitiveComplexCharacter)
    (U c X h : ℝ) (hX : 0<X) (hh : 0≤h) (hhX : h≤X) :
    zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h ≤
      3*(zeroFamilyEnergy F (fun χ => leftIndices χ U) X h +
        zeroFamilyEnergy F (fun χ => rightGoodIndices χ U c) X h +
        zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h) := by
  let f (χ : PrimitiveComplexCharacter) (i : ℕ) (y : ℝ) :=
    if i=0 then zeroWindow χ (leftIndices χ U) h y
    else if i=1 then zeroWindow χ (rightGoodIndices χ U c) h y
    else zeroWindow χ (rightBadIndices χ U c) h y
  have hp (χ : PrimitiveComplexCharacter) (y : ℝ) :
      (∑ i∈range 3,f χ i y) = zeroWindow χ ((V1 χ).V14 U) h y := by
    rw [zeroWindow_partition χ U c h y]
    norm_num [f,Finset.sum_range_succ]
  have hi (χ : PrimitiveComplexCharacter) (i : ℕ) :
      IntervalIntegrable (fun y => ‖f χ i y‖^2) volume X (2*X) := by
    unfold f
    split_ifs <;> apply ContinuousOn.intervalIntegrable_of_Icc (by linarith) <;>
      exact (V6e _ (V1 χ).zeros X h hX hh hhX).norm.pow 2
  unfold zeroFamilyEnergy
  rw [← sum_add_distrib,← sum_add_distrib,mul_sum]
  apply sum_le_sum
  intro χ _
  have hs := V1dr (range 3) (f χ) X hX.le (fun i _ => hi χ i)
  simp_rw [hp] at hs
  simpa [f,Finset.sum_range_succ] using hs

/-- Existing zero density bounds close the entire good part, leaving
only the explicitly filtered near-one packet. -/
theorem fullSpectrumEnergyWithResidual (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ), 1≤Q → X₀≤X → 0<h → h≤X →
      (Q:ℝ)^2/(h/X)≤X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ∈F,χ.modulus≤Q) →
      let U := (2:ℝ)^(K+1)
      let c := 1-V1l.V2j (B+4) X
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h ≤
        C*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
        3*zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := V9h.V1jv B
  obtain ⟨C₂,hC₂,X₂,_,h₂⟩ := goodZerosAllHeights B
  refine ⟨3*(C₁+C₂),by positivity,max 2 (max X₁ X₂),le_max_left ..,?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF
  dsimp only
  let U := (2:ℝ)^(K+1)
  let c := 1-V1l.V2j (B+4) X
  have hX1 : X₁≤X := (le_max_left X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hX2 : X₂≤X := (le_max_right X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hXge : 2≤X := (le_max_left _ _).trans hX
  have hXp : 0<X := by linarith
  have hL : 0<Real.log X := Real.log_pos (by linarith)
  have hleft := h₁ Q hQ K X h hX1 hh hhX hscale hlog F hF
    (fun χ => leftIndices χ U)
    (fun χ _ => filter_subset _ _) (fun χ _ i hi => by simpa only [one_div] using (mem_filter.mp hi).2)
  have hright := h₂ Q K X h hQ hX2 hh hhX hscale hlog F hF
    (fun χ => rightGoodIndices χ U c)
    (fun χ _ => filter_subset _ _)
    (fun χ _ i hi => ⟨by simpa only [one_div] using (mem_filter.mp hi).2.1.le,(mem_filter.mp hi).2.2⟩)
  have hleft' : zeroFamilyEnergy F (fun χ => leftIndices χ U) X h ≤
      C₁*h^2*X/(Real.log X)^B := hleft
  have hright' : zeroFamilyEnergy F (fun χ => rightGoodIndices χ U c) X h ≤
      C₂*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := hright
  have hk : (1:ℝ)≤((K+1:ℕ):ℝ) := by exact_mod_cast (show 1≤K+1 by omega)
  have hleft'' : zeroFamilyEnergy F (fun χ => leftIndices χ U) X h ≤
      C₁*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
    apply hleft'.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hXp.le
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg h)
    calc
      C₁ = C₁*1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hk,sq_nonneg (((K+1:ℕ):ℝ)-1)]) hC₁.le
  calc
    _ ≤ _ := fullSpectrumSplit F U c X h hXp hh.le hhX
    _ ≤ 3*(C₁*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
      C₂*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
      zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h) :=
      mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add hleft'' hright') _)
        (by norm_num)
    _ = _ := by ring


/-- Any fixed positive strip gap, not only 7/8, eliminates the bad packet
eventually. The input is a genuine hypothesis and is not assumed by the
unconditional residual theorem. -/
theorem eventually_badIndices_empty_of_uniform_gap (A : ℕ)
    (σ : ℝ) (hσ : σ < 1)
    (hgap : ∀ (χ : PrimitiveComplexCharacter) (i : ℕ),
      ((V1 χ).zeros i).re ≤ σ) :
    ∀ᶠ X : ℝ in atTop, ∀ (χ : PrimitiveComplexCharacter) (U : ℝ),
      rightBadIndices χ U (1-V1l.V2j A X)=∅ := by
  have ht : Tendsto (fun X : ℝ => Real.log (Real.log X) / Real.log X)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hc : Tendsto (V1l.V2j A) atTop (𝓝 0) := by
    have hm := ht.const_mul (3 * (A+14 : ℕ) : ℝ)
    simp only [mul_zero] at hm
    convert hm using 1
    ext X
    simp only [V1l.V2j, mul_div_assoc]
  filter_upwards [hc.eventually (gt_mem_nhds (sub_pos.mpr hσ))] with X hδ
  intro χ U
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hbad := (Finset.mem_filter.mp hi).2.2
  linarith [hgap χ i]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorPrimeSpectralTransfer.lean; sha256 4237cac1e58a0b9e150fdb7b9180da7e4d37008f19ddc3376b178c8b3098210b -/
section
/-!
Use the smoothed explicit formula directly for the log-prime window.
The von Mangoldt-to-prime correction is absorbed pointwise in E; there
is no extra integral triangle or integrability obligation for the
arithmetic step functions.
-/
open Finset MeasureTheory Filter
open scoped Classical Interval Topology
open OAI.Ostmann V1e V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem primitivePrimeEnergyFromZeros :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (X δ U : ℝ) (h : ℕ), 4 ≤ X → (h:ℝ) ≤ X →
      1 ≤ δ → δ ≤ X/2 → 2 ≤ U → (Q:ℝ) ≤ X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) + 2*Real.sqrt (3*X)*Real.log (3*X)
      (∑ χ∈F, ∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*(Q:ℝ)^2*E^2 +
          2*(∑ χ∈F, ∫ y in X-δ..2*X,
            ‖∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)‖^2) := by
  obtain ⟨D,hD,hformula⟩ := PolynomialWindow.nonprincipalWindowFormulaPolynomial
  refine ⟨D,hD,?_⟩
  intro Q hQ X δ U h hX hhX hδ hδX hU hQX F hF
  dsimp only
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) + 2*Real.sqrt (3*X)*Real.log (3*X)
  let f (χ : PrimitiveComplexCharacter) (y : ℝ) :=
    ∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)
  have hE : 0 ≤ E := by
    have hL : 0≤Real.log X := Real.log_nonneg (by linarith)
    have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
    have hL2 : 0≤Real.log ((Q:ℝ)*U) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQr (by linarith))
    have hL3 : 0≤Real.log (3*X) := Real.log_nonneg (by linarith)
    dsimp [E]
    positivity
  have hcont (χ : PrimitiveComplexCharacter) :
      ContinuousOn (f χ) (Set.Icc (X-δ) (2*X)) := by
    unfold f
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hp : y+(h:ℝ) ≠ 0 := by linarith [hy.1, Nat.cast_nonneg (α := ℝ) h]
      have hc : ContinuousAt (fun t:ℝ => t+(h:ℝ)) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t : ℝ => ((t+(h:ℝ):ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+(h:ℝ)) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+(h:ℝ)) ((V1 χ).zeros i) (Or.inr hp)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y≠0))).continuousWithinAt
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ∈F) :
      (∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2) :=
    windowFormulaEnergy (fun y => InnerFloorAP.centeredPrimeSum χ.character y h) (f χ) (by linarith) (by linarith) hE
      (hcont χ) (fun y hy =>
        by
          have ha := hformula Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ (hF χ hχ)
          have hb := (centeredPrimeWindowError χ h
            (by linarith [hy.1]) (show y+(h:ℝ)≤3*X by linarith [hy.2])).trans
            (Chebyshev.psi_sub_theta_le (show 1≤3*X by linarith))
          have hdiff : ‖InnerFloorAP.centeredPrimeSum χ.character y h - V4q χ h y‖ ≤
              2*Real.sqrt (3*X)*Real.log (3*X) := by
            rw [norm_sub_rev]
            exact hb
          have hsplit : InnerFloorAP.centeredPrimeSum χ.character y h + V3q (f χ) δ y =
              (V4q χ h y + V3q (f χ) δ y) +
                (InnerFloorAP.centeredPrimeSum χ.character y h - V4q χ h y) := by abel
          rw [hsplit]
          exact (norm_add_le _ _).trans (add_le_add ha hdiff))
  have hcard : (F.card:ℝ)≤(Q:ℝ)^2 := by exact_mod_cast V14i F Q hF
  change _ ≤ 2*X*(Q:ℝ)^2*E^2 + 2*(∑ χ∈F, ∫ y in X-δ..2*X,‖f χ y‖^2)
  calc
    _ ≤ ∑ χ∈F, (2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2)) :=
      sum_le_sum hterm
    _ = (F.card:ℝ)*(2*X*E^2)+2*(∑ χ∈F,∫ y in X-δ..2*X,‖f χ y‖^2) := by
      rw [sum_add_distrib,← mul_sum]
      simp only [sum_const,nsmul_eq_mul]
      rw [← mul_sum]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hcard (by positivity : 0≤2*X*E^2)
      linarith


/-- The enlarged smoothing interval is covered by two adjacent dyadic
intervals, so no unproved estimate on a non-dyadic segment is needed. -/
theorem enlargedZeroWindowEnergy_le
    (F : Finset PrimitiveComplexCharacter) (U X h δ : ℝ)
    (hX : 0 < X) (hh : 0 ≤ h) (hhX : h≤X/2)
    (hδ : 0≤δ) (hδX : δ≤X/2) :
    (∑ χ∈F, ∫ y in X-δ..2*X, ‖zeroWindow χ ((V1 χ).V14 U) h y‖^2) ≤
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) (X/2) h +
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h := by
  unfold zeroFamilyEnergy
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro χ _
  let f (y:ℝ) := ‖zeroWindow χ ((V1 χ).V14 U) h y‖^2
  have hcont : ContinuousOn f (Set.Icc (X/2) (2*X)) := by
    unfold f
    apply ContinuousOn.pow
    unfold zeroWindow
    apply ContinuousOn.norm
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hp : y+h≠0 := by linarith [hy.1]
      have hc : ContinuousAt (fun t:ℝ => t+h) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t:ℝ => ((t+h:ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+h) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+h) ((V1 χ).zeros i) (Or.inr hp)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y≠0))).continuousWithinAt
  have hi : IntervalIntegrable f volume (X/2) (2*X) :=
    hcont.intervalIntegrable_of_Icc (by linarith)
  have hsplit : (∫ y in X/2..2*X,f y) =
      (∫ y in X/2..X,f y)+(∫ y in X..2*X,f y) := by
    have h₁ : IntervalIntegrable f volume (X/2) X :=
      (hcont.mono (Set.Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc (by linarith)
    have h₂ : IntervalIntegrable f volume X (2*X) :=
      (hcont.mono (Set.Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (by linarith)
    exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm
  change (∫ y in X-δ..2*X,f y) ≤
    (∫ y in X/2..2*(X/2),f y)+(∫ y in X..2*X,f y)
  rw [show 2*(X/2)=X by ring,← hsplit]
  rw [intervalIntegral.integral_of_le (by linarith : X-δ≤2*X),
    intervalIntegral.integral_of_le (by linarith : X/2≤2*X)]
  have hI : IntegrableOn f (Set.Ioc (X/2) (2*X)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X/2≤2*X)).1 hi
  exact setIntegral_mono_set hI (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ hy => ⟨by linarith [hy.1],hy.2⟩)


/-- Actual prime energy, with an explicit and isolated exceptional
spectral residual. Both dyadic spectral inputs are theorems, not
hypotheses. The only potentially large terms are the two bad packets. -/
theorem primitivePrimeEnergyWithResidual (B : ℕ) :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∃ X₀ : ℝ, 4 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X δ : ℝ) (h : ℕ), 1 ≤ Q → X₀ ≤ X → 0 < h →
      (h:ℝ) ≤ X/2 → 1 ≤ δ → δ ≤ X/2 → (Q:ℝ) ≤ X →
      (Q:ℝ)^2/((h:ℝ)/(X/2)) ≤ (X/2)^(5/12:ℝ) →
      (Q:ℝ)^2/((h:ℝ)/X) ≤ X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log (X/2) →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F,χ.modulus≤Q) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*X)*Real.log (3*X)
      let R (Y:ℝ) := zeroFamilyEnergy F
        (fun χ => rightBadIndices χ U (1-V1l.V2j (B+4) Y)) Y h
      (∑ χ∈F, ∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*(Q:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X/2)/(Real.log (X/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*X/(Real.log X)^B+
        6*(R (X/2)+R X) := by
  obtain ⟨D,hD,hd⟩ := primitivePrimeEnergyFromZeros
  obtain ⟨C,hC,Y₀,hY₀,hc⟩ := fullSpectrumEnergyWithResidual B
  refine ⟨D,C,hD,hC,max 4 (2*Y₀),le_max_left ..,?_⟩
  intro Q K X δ h hQ hX hh hhX hδ hδX hQX hscale₁ hscale₂ hlog F hF
  dsimp only
  let U := (2:ℝ)^(K+1)
  have hX4 : 4≤X := (le_max_left _ _).trans hX
  have hXp : 0 < X := by linarith
  have hY : Y₀≤X/2 := by linarith [(le_max_right (4:ℝ) (2*Y₀)).trans hX]
  have hY' : Y₀≤X := by linarith
  have hU : 2≤U := by
    dsimp [U]
    rw [pow_succ]
    have hk : (1:ℝ)≤(2:ℝ)^K := one_le_pow₀ (by norm_num)
    nlinarith only [hk]
  have hh' : (0:ℝ) < h := by exact_mod_cast hh
  have hlog' : Real.log ((Q:ℝ)*U)≤2*Real.log X :=
    hlog.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith : 0 < X/2) (by linarith)) (by norm_num))
  have he := hd Q hQ X δ U h hX4 (by linarith) hδ hδX hU hQX F hF
  dsimp only at he
  have hz := enlargedZeroWindowEnergy_le F U X h δ hXp hh'.le hhX (by linarith) hδX
  have h1 := hc Q K (X/2) h hQ hY hh' hhX hscale₁ hlog F hF
  have h2 := hc Q K X h hQ hY' hh' (by linarith) hscale₂ hlog' F hF
  dsimp only at h1 h2
  change (∑ χ∈F, ∫ y in X-δ..2*X,‖zeroWindow χ ((V1 χ).V14 U) h y‖^2) ≤ _ at hz
  unfold zeroWindow at hz
  dsimp only [U] at he hz
  have hZ := hz.trans (add_le_add h1 h2)
  have hT := he.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hZ (by norm_num : (0:ℝ) ≤ 2)))
  exact hT.trans_eq (by ring)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorUniformStripBridge.lean; sha256 2aece9ebc1c75e3c24a407777d535c7b6fc0655f89aa8a39f8820e8d891f1a73 -/
section
/-!
An explicit adapter for the public Dirichlet L-function nonvanishing
statement. It does not import that theorem and does not assert it.
The proof needs an approved unconditional theorem of this exact type
(or a weaker uniform positive strip gap). No new axioms are introduced.
-/
open Finset Filter MeasureTheory
open scoped Classical Interval Topology
open OAI.Ostmann V1e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def DirichletUniformStrip (σ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    σ < s.re → ¬(χ=1 ∧ s=1) → DirichletCharacter.LFunction χ s ≠ 0

theorem uniformStrip_enumeratedGap {σ : ℝ} (hs : DirichletUniformStrip σ) :
    ∀ (χ : PrimitiveComplexCharacter) (i : ℕ),
      ((V1 χ).zeros i).re ≤ σ := by
  intro χ i
  by_contra! hi
  letI : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact hs χ.modulus χ.character ((V1 χ).zeros i) hi
    (fun h => χ.nontrivial h.1) ((V1 χ).actual_zero i)

theorem fullSpectrumEnergy_of_uniformStrip {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ), 1≤Q → X₀≤X → 0 < h → h≤X →
      (Q:ℝ)^2/(h/X)≤X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ∈F,χ.modulus≤Q) →
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 ((2:ℝ)^(K+1))) X h ≤
        C*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,hX₁,hbound⟩ := fullSpectrumEnergyWithResidual B
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp
    (eventually_badIndices_empty_of_uniform_gap (B+4) σ hσ
      (uniformStrip_enumeratedGap hs))
  refine ⟨C,hC,max X₁ X₂,hX₁.trans (le_max_left ..),?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF
  have hb := hbound Q K X h hQ ((le_max_left X₁ X₂).trans hX)
    hh hhX hscale hlog F hF
  dsimp only at hb
  have hz : zeroFamilyEnergy F
      (fun χ => rightBadIndices χ ((2:ℝ)^(K+1)) (1-V1l.V2j (B+4) X)) X h = 0 := by
    unfold zeroFamilyEnergy
    apply sum_eq_zero
    intro χ _
    dsimp only
    rw [hX₂ X ((le_max_right X₁ X₂).trans hX) χ ((2:ℝ)^(K+1))]
    simp [zeroWindow]
  rw [hz,mul_zero,add_zero] at hb
  exact hb

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorActualFamilyBlock.lean; sha256 dedf330dfe9d8457875cf64046a38be2c0dce32a9cdafa44fe5f21fe64f3381a -/
section
/-!
The actual arithmetic family on an integer dyadic block, including the
principal character. This uses the exact step-integral identity, rather
than assuming measurability of a new family or losing a logarithm.
The nonprincipal exceptional spectral residual is not removed here.
-/
open Finset MeasureTheory Filter OAI.Ostmann
open scoped Classical Interval Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem actualNonprincipalBlock_eq_integral (A X h : ℕ) :
    (∑ y∈Ico X (2*X),∑ χ∈analyticPrimitiveFamily A,
        ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) =
      ∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ), ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro χ hχ
  have H := integer_step_integral X (2*X) (by omega)
    (fun y : ℝ => ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)
    (fun y : ℕ => ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)
    (by
      intro k y hy
      rw [centeredPrimeSum_on_unit χ.character k h hy])
  push_cast at H
  exact H.symm

theorem actualPrimitiveBlockWithNonprincipal :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (A X h : ℕ), X₀≤(X:ℝ) → h≤X →
        (2*(X:ℝ))^(4/5:ℝ)≤(h:ℝ) →
      (∑ y∈Ico X (2*X), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
      (∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ), ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) +
      C*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨C,hC,X₀,hX₀,hCbound⟩ := principalPrimeWindowLogFour
  refine ⟨C^2,by positivity,X₀,hX₀,?_⟩
  intro A X h hX hhX hhlow
  have hX2 : (2:ℝ)≤X := hX₀.trans hX
  have hXp : (0:ℝ) < X := by linarith
  have hlogX : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  let P (y : ℕ) := ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖^2
  have hp (y : ℕ) (hy : y∈Ico X (2*X)) :
      P y≤(C*(h:ℝ)/(Real.log (X:ℝ))^4)^2 := by
    have hy₁ : (X:ℝ)≤y := by exact_mod_cast (mem_Ico.mp hy).1
    have hy₂ : (y:ℝ)≤2*(X:ℝ) := by exact_mod_cast (mem_Ico.mp hy).2.le
    have hylow : (y:ℝ)^(4/5:ℝ)≤(h:ℝ) :=
      (Real.rpow_le_rpow (by positivity) hy₂ (by norm_num)).trans hhlow
    have hyh : (h:ℝ)≤y := (by exact_mod_cast hhX : (h:ℝ)≤X).trans hy₁
    have he := hCbound y (hX.trans hy₁) h hylow hyh (1:DirichletCharacter ℂ 1)
    have hl : Real.log (X:ℝ)≤Real.log (y:ℝ) := Real.log_le_log hXp hy₁
    have hden : (Real.log (X:ℝ))^4≤(Real.log (y:ℝ))^4 :=
      pow_le_pow_left₀ hlogX.le hl 4
    have hb : ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖ ≤
        C*(h:ℝ)/(Real.log (X:ℝ))^4 :=
      he.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hlogX _) hden)
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hP : (∑ y∈Ico X (2*X),P y) ≤
      C^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
    calc
      _ ≤ ∑ _y∈Ico X (2*X),(C*(h:ℝ)/(Real.log (X:ℝ))^4)^2 := sum_le_sum hp
      _ = _ := by
        rw [sum_const,nsmul_eq_mul,Nat.card_Ico,show 2*X-X=X by omega]
        ring
  calc
    _ ≤ ∑ y∈Ico X (2*X),
        ((∑ χ∈analyticPrimitiveFamily A,
          ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)+P y) :=
      sum_le_sum fun y _ => primitiveEnergy_le_analyticFamily A y h
    _ = (∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ),‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) +
        ∑ y∈Ico X (2*X),P y := by
      rw [sum_add_distrib,actualNonprincipalBlock_eq_integral]
    _ ≤ _ := add_le_add le_rfl hP

/-- Direct actual arithmetic block bound. No unknown arithmetic family
or all-residue model appears: only the two explicitly defined spectral
residuals remain. -/
theorem actualPrimitiveBlockWithResidual (B : ℕ) :
    ∃ D C P : ℝ, 0 < D ∧ 0 < C ∧ 0 < P ∧ ∃ X₀ : ℝ, 4≤X₀ ∧
      ∀ (A X h K : ℕ) (δ : ℝ), 1≤A → X₀≤(X:ℝ) → 0 < h →
      (2*(X:ℝ))^(4/5:ℝ)≤(h:ℝ) → (h:ℝ)≤(X:ℝ)/2 →
      1≤δ → δ≤(X:ℝ)/2 → A≤X →
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2))≤((X:ℝ)/2)^(5/12:ℝ) →
      (A:ℝ)^2/((h:ℝ)/(X:ℝ))≤(X:ℝ)^(5/12:ℝ) →
      Real.log ((A:ℝ)*(2:ℝ)^(K+1))≤2*Real.log ((X:ℝ)/2) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
      let R (Y:ℝ) := zeroFamilyEnergy (analyticPrimitiveFamily A)
        (fun χ => rightBadIndices χ U (1-V1l.V2j (B+4) Y)) Y h
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        2*(X:ℝ)*(A:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*((X:ℝ)/2)/(Real.log ((X:ℝ)/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^B+
        6*(R ((X:ℝ)/2)+R X)+
        P*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨D,C,hD,hC,X₁,hX₁,hbound⟩ := primitivePrimeEnergyWithResidual B
  obtain ⟨P,hP,X₂,hX₂,hprincipal⟩ := actualPrimitiveBlockWithNonprincipal
  refine ⟨D,C,P,hD,hC,hP,max X₁ X₂,hX₁.trans (le_max_left ..),?_⟩
  intro A X h K δ hA hX hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  dsimp only
  have hX₁' : X₁≤(X:ℝ) := (le_max_left _ _).trans hX
  have hX₂' : X₂≤(X:ℝ) := (le_max_right _ _).trans hX
  have hh' : h≤X := by
    exact_mod_cast hhX.trans (by linarith [Nat.cast_nonneg (α:=ℝ) X] : (X:ℝ)/2≤X)
  have H := hprincipal A X h hX₂' hh' hlow
  have G := hbound A K X δ h hA hX₁' hh hhX hδ hδX
    (by exact_mod_cast hAX) hs₁ hs₂ hlog (analyticPrimitiveFamily A)
      (analyticPrimitiveFamily_modulus A)
  dsimp only at G
  exact H.trans (add_le_add G le_rfl)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorUniformStripArithmetic.lean; sha256 46a990b4e8a7cd3d01559216b61bb11bb71a6bdc4e808bf658ffd213819dfc5a -/
section
/-! The actual primitive arithmetic family estimate with the sole
remaining analytic input, a uniform positive zero-free strip.
This is an implication, not a proof of the strip or frozen floor. -/
open Filter Finset MeasureTheory OAI.Ostmann
open scoped Classical Interval Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem actualPrimitiveBlockOfUniformStrip {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) (B : ℕ) :
    ∃ D C P : ℝ, 0 < D ∧ 0 < C ∧ 0 < P ∧ ∃ X₀ : ℝ, 4 ≤ X₀ ∧
      ∀ (A X h K : ℕ) (δ : ℝ), 1 ≤ A → X₀ ≤ (X:ℝ) → 0 < h →
      (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) → (h:ℝ) ≤ (X:ℝ)/2 →
      1 ≤ δ → δ ≤ (X:ℝ)/2 → A ≤ X →
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2)) ≤ ((X:ℝ)/2)^(5/12:ℝ) →
      (A:ℝ)^2/((h:ℝ)/(X:ℝ)) ≤ (X:ℝ)^(5/12:ℝ) →
      Real.log ((A:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log ((X:ℝ)/2) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        2*(X:ℝ)*(A:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*((X:ℝ)/2)/(Real.log ((X:ℝ)/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^B+
        P*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨D,C,P,hD,hC,hP,X₁,hX₁,hbound⟩ := actualPrimitiveBlockWithResidual B
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp
    (eventually_badIndices_empty_of_uniform_gap (B+4) σ hσ
      (uniformStrip_enumeratedGap hs))
  refine ⟨D,C,P,hD,hC,hP,max X₁ (2*max X₂ 1),hX₁.trans (le_max_left ..),?_⟩
  intro A X h K δ hA hX hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  have hx₁ : X₁ ≤ (X:ℝ) := (le_max_left _ _).trans hX
  have hx₂ : X₂ ≤ (X:ℝ)/2 := by
    have H := (le_max_right X₁ (2*max X₂ 1)).trans hX
    linarith only [H,le_max_left X₂ 1]
  have hx₂' : X₂ ≤ (X:ℝ) := by linarith only [hx₂,Nat.cast_nonneg (α:=ℝ) X]
  have G := hbound A X h K δ hA hx₁ hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  dsimp only at G ⊢
  have hz (Y : ℝ) (hY : X₂ ≤ Y) :
      zeroFamilyEnergy (analyticPrimitiveFamily A)
        (fun χ => rightBadIndices χ ((2:ℝ)^(K+1)) (1-V1l.V2j (B+4) Y)) Y h = 0 := by
    unfold zeroFamilyEnergy
    apply sum_eq_zero
    intro χ _
    dsimp only
    rw [hX₂ Y hY χ ((2:ℝ)^(K+1))]
    simp [zeroWindow]
  rw [hz _ hx₂,hz _ hx₂',add_zero,mul_zero,add_zero] at G
  exact G

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorWindowScale.lean; sha256 67b13ea87fca3619b3991bcfb84e0ca10f1f55d1e31dfa992d4b03ab4a69acdf -/
section
open Filter Finset
open scoped Topology

namespace InnerFloorResearch

noncomputable section

abbrev innerCutoff := GoldbachGRHBudget.narrow
noncomputable abbrev outerCutoff := GoldbachGRHBudget.cutoff

def innerWidth (n : ℕ) : ℝ := (innerCutoff n : ℝ) * (n : ℝ) ^ (1/6 : ℝ)
def middleCutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1/5 : ℝ)⌋₊
def innerWindow (n : ℕ) : ℕ := ⌊(n : ℝ) / (12 * innerWidth n)⌋₊

private theorem narrow_le_log (n : ℕ) (hn : 2 ≤ n) :
    (innerCutoff n : ℝ) ≤ 16 * (Real.log (n : ℝ)) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ (Nat.log 2 (n+2)) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n : ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2
    (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0 ≤ (_ : ℝ))
  have hL : (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    push_cast at hraw hlog
    linarith only [hraw, hlog, hm]
  unfold innerCutoff GoldbachGRHBudget.narrow
  push_cast
  calc
    _ ≤ (4 * Real.log (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
    _ = _ := by ring

/-- The real inner radius fits the frozen wide-arc budget. -/
theorem eventualInnerGeometry : ∀ᶠ n : ℕ in atTop,
    2 ≤ n ∧ 1 ≤ innerCutoff n ∧ innerCutoff n ≤ middleCutoff n ∧
    middleCutoff n ≤ outerCutoff n ∧ innerWidth n ≤ (GoldbachGRHBudget.width n : ℝ) ∧
    2 * (GoldbachGRHBudget.width n : ℝ) * (outerCutoff n : ℝ) < (n : ℝ) := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/5) (1/16) (by norm_num) (by norm_num)]
    with n hg hlog
  obtain ⟨hn, hQ, hQB, _, _, hbudget⟩ := hg
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hQA : innerCutoff n ≤ middleCutoff n := by
    apply Nat.le_floor
    calc
      _ ≤ 16 * (Real.log (n : ℝ))^2 := narrow_le_log n hn
      _ ≤ (n : ℝ)^(1/5 : ℝ) := by linarith
  have hAB : middleCutoff n ≤ outerCutoff n := by
    apply Nat.floor_mono
    exact Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  have hB1 : (1 : ℝ) ≤ outerCutoff n := by exact_mod_cast hQ.trans hQB
  have h6 : (n : ℝ)^(1/6 : ℝ) ≤ 2 * (outerCutoff n : ℝ) := by
    have hf := Nat.lt_floor_add_one ((n : ℝ)^(1/3 : ℝ))
    change (n : ℝ)^(1/3 : ℝ) < (outerCutoff n : ℝ) + 1 at hf
    exact (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)).trans
      (show (n : ℝ)^(1/3 : ℝ) ≤ 2 * (outerCutoff n : ℝ) by linarith)
  refine ⟨hn, hQ, hQA, hAB, ?_, ?_⟩
  · unfold innerWidth GoldbachGRHBudget.width
    push_cast
    have hQ₀ : 0 ≤ (innerCutoff n : ℝ) := Nat.cast_nonneg _
    have hB₀ : 0 ≤ (outerCutoff n : ℝ) := Nat.cast_nonneg _
    nlinarith only [mul_le_mul_of_nonneg_left h6 hQ₀, mul_nonneg hQ₀ hB₀]
  · exact_mod_cast hbudget

/-- One common window for all inner-arc denominators, with a power margin
in the high-exponent short-progression hypothesis. -/
theorem eventualInnerWindow : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (4/5 : ℝ) ≤ (innerWindow n : ℝ) ∧ innerWindow n ≤ n ∧
    6 * (innerWindow n : ℝ) * innerWidth n ≤ (n : ℝ) := by
  filter_upwards [eventualInnerGeometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/30) (1/384) (by norm_num) (by norm_num)]
    with n hg hlog
  obtain ⟨hn, hQ, _, _, _, _⟩ := hg
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hQ' : (1 : ℝ) ≤ innerCutoff n := by exact_mod_cast hQ
  have hu : 0 < innerWidth n :=
    mul_pos (zero_lt_one.trans_le hQ') (Real.rpow_pos_of_pos hn0 _)
  have hu1 : 1 ≤ innerWidth n :=
    one_le_mul_of_one_le_of_one_le hQ' (Real.one_le_rpow hnR (by norm_num))
  have hQsmall : 384 * (Real.log (n : ℝ))^2 ≤ (n : ℝ)^(1/30 : ℝ) := by
    linarith
  have hwidth : 24 * innerWidth n ≤ (n : ℝ)^(1/5 : ℝ) := by
    have hs : 24 * (innerCutoff n : ℝ) ≤ (n : ℝ)^(1/30 : ℝ) := by
      linarith only [narrow_le_log n hn, hQsmall]
    calc
      _ = (24 * (innerCutoff n : ℝ)) * (n : ℝ)^(1/6 : ℝ) := by unfold innerWidth; ring
      _ ≤ (n : ℝ)^(1/30 : ℝ) * (n : ℝ)^(1/6 : ℝ) :=
        mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hdiv : 2 * (n : ℝ)^(4/5 : ℝ) ≤ (n : ℝ)/(12 * innerWidth n) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ = (24 * innerWidth n) * (n : ℝ)^(4/5 : ℝ) := by ring
      _ ≤ (n : ℝ)^(1/5 : ℝ) * (n : ℝ)^(4/5 : ℝ) :=
        mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hf := Nat.lt_floor_add_one ((n : ℝ)/(12 * innerWidth n))
  change (n : ℝ)/(12 * innerWidth n) < (innerWindow n : ℝ) + 1 at hf
  have h1 : 1 ≤ (n : ℝ)^(4/5 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  have hfloor : (innerWindow n : ℝ) ≤ (n : ℝ)/(12 * innerWidth n) :=
    Nat.floor_le (by positivity)
  have hn' : (innerWindow n : ℝ) ≤ (n : ℝ) :=
    hfloor.trans (div_le_self hn0.le (by linarith))
  have hmul := (le_div_iff₀ (show 0 < 12 * innerWidth n by positivity)).1 hfloor
  exact ⟨by linarith, by exact_mod_cast hn', by nlinarith only [hmul, hn0]⟩

theorem sharpModulusBudget {n x h : ℕ} {t : ℝ} (hn : 1 ≤ n) (hx : 1 ≤ x)
    (hxn : x ≤ n) (hlo : (n : ℝ)^(4/5 : ℝ) ≤ (h : ℝ))
    (ht : (4/5 : ℝ) ≤ t) (ht' : t ≤ 1) :
    (outerCutoff n : ℝ)^2 * (x : ℝ)^((1-t)/3+1/16) ≤ (h : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxnR : (x : ℝ) ≤ n := by exact_mod_cast hxn
  have hB : (outerCutoff n : ℝ) ≤ (n : ℝ)^(1/3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hp : (x : ℝ)^((1-t)/3+1/16) ≤ (n : ℝ)^(31/240 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hxR (by linarith)).trans
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hxnR (by norm_num))
  calc
    _ ≤ ((n : ℝ)^(1/3 : ℝ))^2 * (n : ℝ)^(31/240 : ℝ) :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2) hp
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
    _ = (n : ℝ)^(191/240 : ℝ) := by
      rw [pow_two, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
      norm_num
    _ ≤ (n : ℝ)^(4/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
    _ ≤ _ := hlo

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorFixedPowerBands.lean; sha256 9a869bc8a7ee62f43c97b6c87b3b9c5776f115bebca902b4927ef6fa27565b88 -/
section
/-!
Ten fixed exponent bands rather than O(log n) dyadic denominator bands.
The first lower denominator is at least the frozen narrow cutoff;
each subsequent endpoint is floor(n^(j/50)). A constant number of
bands is enough because the explicit-formula scale inequalities have
strict exponent slack even at the top endpoint 1/5.

This is only the parameter/partition step, not the zero-free theorem.
-/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def fixedBandLowerExp (j : ℕ) : ℝ := (j:ℝ)/50
def fixedBandUpperExp (j : ℕ) : ℝ := ((j+1:ℕ):ℝ)/50
def fixedBandWindowExp (j : ℕ) : ℝ :=
  min (5/6 + fixedBandLowerExp j - 1/100) (99/100)

def fixedBandEnd (n j : ℕ) : ℕ :=
  max (innerCutoff n) ⌊(n:ℝ)^(fixedBandLowerExp j)⌋₊

def fixedBandWindow (n j : ℕ) : ℕ :=
  ⌊(n:ℝ)^(fixedBandWindowExp j)⌋₊

/-- All relevant exponent inequalities have explicit slack. In particular,
the worst density scale is the last band and still saves 1/150. -/
theorem fixedBandExponents (j : ℕ) (hj : j < 10) (b : ℝ)
    (hb : fixedBandWindowExp j - 1/1000 ≤ b) (hb' : b ≤ 1) :
    0 ≤ fixedBandLowerExp j ∧
    fixedBandUpperExp j ≤ 1/5 ∧
    4/5+1/100 ≤ fixedBandWindowExp j ∧
    fixedBandWindowExp j ≤ 99/100 ∧
    fixedBandWindowExp j + 1/100 ≤ 5/6 + fixedBandLowerExp j ∧
    2*fixedBandUpperExp j+(7/12)*b-fixedBandWindowExp j ≤ -1/150 ∧
    fixedBandUpperExp j+(2/3)*b-fixedBandWindowExp j ≤ -1/10 ∧
    fixedBandUpperExp j-b/6-fixedBandWindowExp j ≤ -1/10 ∧
    3*fixedBandUpperExp j-b/6-fixedBandWindowExp j ≤ -1/10 ∧
    fixedBandUpperExp j+b/2-fixedBandWindowExp j ≤ -1/4 ∧
    fixedBandUpperExp j-b/2 ≤ -1/10 := by
  interval_cases j <;>
    norm_num [fixedBandLowerExp,fixedBandUpperExp,fixedBandWindowExp,min_def] at * <;>
    (repeat' (first | apply And.intro | linarith))

theorem fixedBandEnd_mono (n : ℕ) (hn : 1 ≤ n) :
    Monotone (fixedBandEnd n) := by
  intro j k hjk
  unfold fixedBandEnd
  apply max_le_max le_rfl
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  unfold fixedBandLowerExp
  gcongr

theorem fixedBandEnd_zero (n : ℕ) (hQ : 1 ≤ innerCutoff n) :
    fixedBandEnd n 0=innerCutoff n := by
  simp [fixedBandEnd,fixedBandLowerExp,max_eq_left hQ]

theorem fixedBandEnd_ten (n : ℕ) (hQA : innerCutoff n ≤ middleCutoff n) :
    fixedBandEnd n 10=middleCutoff n := by
  have he : fixedBandLowerExp 10=1/5 := by norm_num [fixedBandLowerExp]
  rw [fixedBandEnd,he]
  exact max_eq_right hQA

theorem fixedBandWindow_bounds (n j : ℕ) (hn : 1 ≤ n) (hj : j < 10) :
    fixedBandWindow n j ≤ n ∧
    (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^(99/100:ℝ) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hc : fixedBandWindowExp j ≤ (99/100:ℝ) := min_le_right _ _
  have hf : (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hh := hf.trans (Real.rpow_le_rpow_of_exponent_le hn' hc)
  have hn'': (fixedBandWindow n j:ℝ) ≤ (n:ℝ) := hh.trans (by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hn' (show (99/100:ℝ) ≤ 1 by norm_num)))
  exact ⟨Nat.cast_le.mp hn'',hh⟩

/-- The ten widths all satisfy the exact Gallagher frequency condition
and the uniform lower bound needed for the principal prime window.
The cap n^.99 gives a polynomial boundary saving, not just a log cap. -/
theorem eventualFixedBandWindows : ∀ᶠ n : ℕ in atTop,
    ∀ j < 10,
      (n:ℝ)^(4/5:ℝ) ≤ (fixedBandWindow n j:ℝ) ∧
      (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^(99/100:ℝ) ∧
      6*(fixedBandWindow n j:ℝ)*innerWidth n ≤ (fixedBandEnd n j:ℝ)*n := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htiny := (tendsto_rpow_atTop (show (0:ℝ) < 1/100 by norm_num)).comp ht
  filter_upwards [eventualInnerGeometry,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/100) (1/192) (by norm_num) (by norm_num),
    htiny.eventually_ge_atTop 2] with n hg hlog hsmall
  intro j hj
  obtain ⟨hn,hQ,hQA,hAB,huH,hsep⟩ := hg
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hc : (4/5+1/100:ℝ) ≤ fixedBandWindowExp j := by
    unfold fixedBandWindowExp fixedBandLowerExp
    apply le_min <;> linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hres : fixedBandWindowExp j+1/100 ≤ 5/6+fixedBandLowerExp j := by
    unfold fixedBandWindowExp
    linarith only [min_le_left (5/6+fixedBandLowerExp j-1/100) (99/100:ℝ)]
  have hf := Nat.lt_floor_add_one ((n:ℝ)^fixedBandWindowExp j)
  change (n:ℝ)^fixedBandWindowExp j < (fixedBandWindow n j:ℝ)+1 at hf
  have hlower : 2*(n:ℝ)^(4/5:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j := by
    calc
      _ ≤ (n:ℝ)^(1/100:ℝ)*(n:ℝ)^(4/5:ℝ) :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hnP.le _)
      _ = (n:ℝ)^(4/5+1/100:ℝ) := by rw [← Real.rpow_add hnP]; congr 1 <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR hc
  have h1 := Real.one_le_rpow hnR (show (0:ℝ) ≤ 4/5 by norm_num)
  have hf' : (fixedBandWindow n j:ℝ) ≤ (n:ℝ)^fixedBandWindowExp j :=
    Nat.floor_le (Real.rpow_nonneg hnP.le _)
  have hQlog : (innerCutoff n:ℝ) ≤ 16*(Real.log (n:ℝ))^2 := by
    -- Public re-use of the bound through the exact narrow definition.
    have hp : (2:ℝ)^Nat.log 2 (n+2) ≤ ((n+2:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2≠0)
    have hraw := Real.log_le_log (by positivity) hp
    have hin : ((n+2:ℕ):ℝ) ≤ (n:ℝ)^2 := by
      push_cast
      nlinarith only [(show (2:ℝ) ≤ n by exact_mod_cast hn),sq_nonneg ((n:ℝ)-2)]
    have hlog' := Real.log_le_log (by positivity) hin
    rw [Real.log_pow] at hraw hlog'
    have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2)))
    have hL : (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
      push_cast at hraw hlog'
      linarith only [hraw,hlog',hm]
    unfold innerCutoff GoldbachGRHBudget.narrow
    push_cast
    calc
      _ ≤ (4*Real.log n)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
      _ = _ := by ring
  have hQsmall : 12*(innerCutoff n:ℝ) ≤ (n:ℝ)^(1/100:ℝ) := by
    linarith only [hQlog,hlog]
  have hD : (n:ℝ)^fixedBandLowerExp j ≤ 2*(fixedBandEnd n j:ℝ) := by
    have hp := Nat.lt_floor_add_one ((n:ℝ)^fixedBandLowerExp j)
    have hm : (⌊(n:ℝ)^fixedBandLowerExp j⌋₊:ℝ) ≤ (fixedBandEnd n j:ℝ) := by
      exact_mod_cast le_max_right (innerCutoff n) ⌊(n:ℝ)^fixedBandLowerExp j⌋₊
    have hD1 : (1:ℝ) ≤ fixedBandEnd n j := by
      exact_mod_cast hQ.trans (le_max_left _ _)
    linarith
  refine ⟨by linarith,(fixedBandWindow_bounds n j (by omega) hj).2,?_⟩
  have hpow : (n:ℝ)^(fixedBandWindowExp j+1/100+1/6) ≤ (n:ℝ)^(1+fixedBandLowerExp j) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  calc
    _ = (12*(innerCutoff n:ℝ))*(fixedBandWindow n j:ℝ)*(n:ℝ)^(1/6:ℝ)/2 := by
      unfold innerWidth
      ring
    _ ≤ ((n:ℝ)^(1/100:ℝ)*(n:ℝ)^fixedBandWindowExp j)*(n:ℝ)^(1/6:ℝ)/2 := by
      gcongr
    _ = (n:ℝ)^(fixedBandWindowExp j+1/100+1/6)/2 := by
      rw [← Real.rpow_add hnP,← Real.rpow_add hnP]
      congr 2 <;> ring
    _ ≤ (n:ℝ)^(1+fixedBandLowerExp j)/2 :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    _ = (n:ℝ)*((n:ℝ)^fixedBandLowerExp j)/2 := by rw [Real.rpow_add hnP,Real.rpow_one]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hD hnP.le]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorFixedBandAnalyticParameters.lean; sha256 925b2e6ba67302be5fe7afd03caf43c3a044ae782d91df5108ec50312718c0a1 -/
section
/-! Use global n-based smoothing and truncation parameters on all
integer dyadic blocks, avoiding an extra local log-scale parameter.
The endpoint exponent a and window exponent c have fixed slack.
No zero-free theorem is assumed or asserted in this file. -/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem fixedBandGlobalExponents (j : ℕ) (hj : j < 10) :
    let a := fixedBandUpperExp j
    let c := fixedBandWindowExp j
    1/50 ≤ a ∧ a ≤ 1/5 ∧ 4/5+1/100 ≤ c ∧
    2*a+7/12 ≤ c-1/150 ∧
    a+3/2 ≤ 2*c-1/10 ∧
    a+2/3 ≤ c-1/10 ∧
    a-1/6 ≤ c-1/10 ∧
    3*a-1/6 ≤ c-1/10 ∧
    a+1/2 ≤ c-1/4 := by
  dsimp only
  interval_cases j <;> norm_num [fixedBandUpperExp,fixedBandWindowExp,
    fixedBandLowerExp,min_def]

private theorem cutoff_log_square (n : ℕ) (hn : 2 ≤ n) :
    (innerCutoff n:ℝ) ≤ 16*(Real.log (n:ℝ))^2 := by
  have hp : (2:ℝ)^Nat.log 2 (n+2) ≤ ((n+2:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2≠0)
  have hraw := Real.log_le_log (by positivity) hp
  have hin : ((n+2:ℕ):ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith only [(show (2:ℝ) ≤ n by exact_mod_cast hn),sq_nonneg ((n:ℝ)-2)]
  have hlog' := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog'
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2)))
  have hL : (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
    push_cast at hraw hlog'
    linarith only [hraw,hlog',hm]
  unfold innerCutoff GoldbachGRHBudget.narrow
  push_cast
  calc
    _ ≤ (4*Real.log n)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
    _ = _ := by ring

theorem eventualFixedBandPowerEndpoints : ∀ᶠ n : ℕ in atTop,
    ∀ j < 10,
      1 ≤ fixedBandEnd n (j+1) ∧
      (fixedBandEnd n (j+1):ℝ) ≤ (n:ℝ)^fixedBandUpperExp j ∧
      (n:ℝ)^fixedBandWindowExp j ≤ 2*(fixedBandWindow n j:ℝ) := by
  filter_upwards [eventualInnerGeometry,eventualFixedBandWindows,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/100) (1/16) (by norm_num) (by norm_num)]
    with n hg hw hlog
  intro j hj
  obtain ⟨hn,hQ,hQA,hAB,huH,hsep⟩ := hg
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hQsmall : (innerCutoff n:ℝ) ≤ (n:ℝ)^(1/100:ℝ) :=
    (cutoff_log_square n hn).trans (by linarith only [hlog])
  have ha : (1/100:ℝ) ≤ fixedBandUpperExp j := by
    unfold fixedBandUpperExp
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hQpow := hQsmall.trans (Real.rpow_le_rpow_of_exponent_le hnR ha)
  have hfl : (⌊(n:ℝ)^fixedBandLowerExp (j+1)⌋₊:ℝ) ≤
      (n:ℝ)^fixedBandUpperExp j :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hA : 1 ≤ fixedBandEnd n (j+1) := hQ.trans (le_max_left _ _)
  have hh1 : (1:ℝ) ≤ fixedBandWindow n j :=
    (Real.one_le_rpow hnR (by norm_num : (0:ℝ) ≤ 4/5)).trans (hw j hj).1
  have hf := Nat.lt_floor_add_one ((n:ℝ)^fixedBandWindowExp j)
  change (n:ℝ)^fixedBandWindowExp j < (fixedBandWindow n j:ℝ)+1 at hf
  refine ⟨hA,?_,by linarith⟩
  unfold fixedBandEnd
  push_cast
  exact max_le hQpow hfl

def fixedTruncationIndex (n : ℕ) : ℕ := Nat.log 2 ⌊(n:ℝ)^(3/2:ℝ)⌋₊

theorem fixedTruncation_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^(3/2:ℝ) ≤ (2:ℝ)^(fixedTruncationIndex n+1) ∧
    (2:ℝ)^(fixedTruncationIndex n+1) ≤ 2*(n:ℝ)^(3/2:ℝ) := by
  let R := (n:ℝ)^(3/2:ℝ)
  let m := ⌊R⌋₊
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hm : 1 ≤ m := Nat.le_floor (Real.one_le_rpow hnR (by norm_num))
  have hupper : (2:ℕ)^(Nat.log 2 m) ≤ m :=
    Nat.pow_log_le_self 2 (by omega)
  have hlower := Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
  have hf := Nat.lt_floor_add_one R
  have hF : (m:ℝ) ≤ R := Nat.floor_le (by dsimp [R]; positivity)
  have hu : (2:ℝ)^(Nat.log 2 m) ≤ (m:ℝ) := by exact_mod_cast hupper
  have hl : (m:ℝ)+1 ≤ (2:ℝ)^(Nat.log 2 m+1) := by
    exact_mod_cast (show m+1 ≤ 2^(Nat.log 2 m+1) by omega)
  change R ≤ (2:ℝ)^(Nat.log 2 m+1) ∧ (2:ℝ)^(Nat.log 2 m+1) ≤ 2*R
  constructor
  · exact hf.le.trans hl
  · rw [pow_succ]
    nlinarith only [hu,hF]

theorem fixedTruncation_logBound (n : ℕ) (hn : 2 ≤ n) :
    ((fixedTruncationIndex n+1:ℕ):ℝ) ≤ 5*Real.log (n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnP : (0:ℝ) < n := by linarith
  have hlog := Real.log_le_log (by positivity) (fixedTruncation_bounds n (by omega)).2
  rw [Real.log_pow,Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hnP _).ne',
    Real.log_rpow hnP] at hlog
  have hL2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL := Real.log_le_log (by norm_num : (0:ℝ) < 2) hnR
  have H := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg (fixedTruncationIndex n+1))
  nlinarith only [hlog,H,hL]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorFixedBlockScale.lean; sha256 70e1ea66fa1c975653e1c542a2f22f205416ab7497f07c6f9441beab780b18bf -/
section
/-! All exact hypotheses of the primitive spectral block theorem from
the fixed exponent band parameters. Global smoothing delta=n^(2/3)
and dyadic truncation U~n^(3/2) work simultaneously for 2h<=X<=n. -/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

private theorem power_reserve {n e c d R : ℝ} (hn : 1 ≤ n)
    (hR : 0 ≤ R) (hsmall : R ≤ n^d) (he : e+d ≤ c) :
    R*n^e ≤ n^c := by
  have hnp : 0 < n := by linarith
  calc
    _ ≤ n^d*n^e := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hnp.le _)
    _ = n^(d+e) := (Real.rpow_add hnp d e).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by linarith)

theorem eventualFixedBlockScale :
    ∀ᶠ n : ℕ in atTop, ∀ j < 10, ∀ X : ℕ,
      let A := fixedBandEnd n (j+1)
      let h := fixedBandWindow n j
      let K := fixedTruncationIndex n
      let δ := (n:ℝ)^(2/3:ℝ)
      2*h ≤ X → X ≤ n →
      1 ≤ A ∧ 0 < h ∧ (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) ∧
      (h:ℝ) ≤ (X:ℝ)/2 ∧ 1 ≤ δ ∧ δ ≤ (X:ℝ)/2 ∧ A ≤ X ∧
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2)) ≤ ((X:ℝ)/2)^(5/12:ℝ) ∧
      (A:ℝ)^2/((h:ℝ)/(X:ℝ)) ≤ (X:ℝ)^(5/12:ℝ) ∧
      Real.log ((A:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log ((X:ℝ)/2) ∧
      (4/5:ℝ)*Real.log (n:ℝ) ≤ Real.log ((X:ℝ)/2) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, (8:ℝ) ≤ (n:ℝ)^(1/150:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/150)).comp ht).eventually
      (eventually_ge_atTop 8)
  filter_upwards [eventually_ge_atTop (2:ℕ), eventualFixedBandWindows,
    eventualFixedBandPowerEndpoints,hsmall] with n hn hw he hp
  intro j hj X
  dsimp only
  intro hhX hXn
  let A := fixedBandEnd n (j+1)
  let h := fixedBandWindow n j
  let K := fixedTruncationIndex n
  let a := fixedBandUpperExp j
  let c := fixedBandWindowExp j
  let δ := (n:ℝ)^(2/3:ℝ)
  let U := (2:ℝ)^(K+1)
  obtain ⟨hA,hAp,hcp⟩ := he j hj
  obtain ⟨hhlo,hhhi,hwidth⟩ := hw j hj
  obtain ⟨ha,ha',hc,hdens,hUexp,hδexp,hneg,hcub,hpp⟩ := fixedBandGlobalExponents j hj
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hA0 : (0:ℝ) < A := by exact_mod_cast (show 0 < fixedBandEnd n (j+1) by omega)
  have hhP : (0:ℝ) < h :=
    (Real.rpow_pos_of_pos hnP (4/5:ℝ)).trans_le hhlo
  have hhN : 0 < h := Nat.cast_pos.mp hhP
  have hhX' : (h:ℝ) ≤ (X:ℝ)/2 := by
    have H : (2:ℝ)*(h:ℝ) ≤ X := by exact_mod_cast hhX
    linarith only [H]
  have hXP : (0:ℝ) < X := by linarith only [hhP,hhX']
  have hXn' : (X:ℝ) ≤ n := by exact_mod_cast hXn
  have hh1 : 1 ≤ (h:ℝ) := (Real.one_le_rpow hnR (by norm_num : (0:ℝ) ≤ 4/5)).trans hhlo
  have hXhalf1 : 1 ≤ (X:ℝ)/2 := hh1.trans hhX'
  have hp' : (8:ℝ) ≤ (n:ℝ)^(1/100:ℝ) :=
    hp.trans (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have hlarge : 4*(n:ℝ)^(4/5:ℝ) ≤ (n:ℝ)^c :=
    power_reserve hnR (by norm_num) (by linarith : (4:ℝ) ≤ (n:ℝ)^(1/100:ℝ))
      (by exact hc)
  have hh4 : 2*(n:ℝ)^(4/5:ℝ) ≤ (h:ℝ) := by linarith only [hlarge,hcp]
  have hlow : (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) := by
    calc
      _ ≤ (2*(n:ℝ))^(4/5:ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2:ℝ)^(4/5:ℝ)*(n:ℝ)^(4/5:ℝ) := Real.mul_rpow (by norm_num) hnP.le
      _ ≤ 2*(n:ℝ)^(4/5:ℝ) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (4/5:ℝ) ≤ 1))
          (Real.rpow_nonneg hnP.le _)
      _ ≤ _ := hh4
  have hδ1 : 1 ≤ δ := Real.one_le_rpow hnR (by norm_num)
  have hδh : δ ≤ (h:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (2/3:ℝ) ≤ 4/5)).trans hhlo
  have hAX : (A:ℝ) ≤ X := calc
    _ ≤ (n:ℝ)^a := hAp
    _ ≤ (n:ℝ)^(4/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [ha'])
    _ ≤ h := hhlo
    _ ≤ _ := by linarith only [hhX',hhP]
  have hds (Y : ℝ) (hY : 0 < Y) (hYn : Y ≤ n) :
      (A:ℝ)^2/((h:ℝ)/Y) ≤ Y^(5/12:ℝ) := by
    have hprod : (A:ℝ)^2*Y^(7/12:ℝ) ≤ (h:ℝ) := by
      calc
        _ ≤ ((n:ℝ)^a)^2*(n:ℝ)^(7/12:ℝ) :=
          mul_le_mul (pow_le_pow_left₀ hA0.le hAp 2)
            (Real.rpow_le_rpow hY.le hYn (by norm_num))
            (Real.rpow_nonneg hY.le _) (sq_nonneg _)
        _ = (n:ℝ)^(2*a+7/12) := by
          rw [pow_two,← Real.rpow_add hnP,← Real.rpow_add hnP]
          congr 1 <;> ring
        _ ≤ (h:ℝ) := by
          have H : 2*(n:ℝ)^(2*a+7/12) ≤ (n:ℝ)^c :=
            power_reserve hnR (by norm_num) (by linarith : (2:ℝ) ≤ (n:ℝ)^(1/150:ℝ))
              (by linarith only [hdens])
          linarith only [H,hcp]
    apply (div_le_iff₀ (div_pos hhP hY)).2
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hY).2
    have H := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hY.le (5/12:ℝ))
    rw [mul_assoc,← Real.rpow_add hY,show (7/12:ℝ)+5/12=1 by norm_num,Real.rpow_one] at H
    simpa only [mul_div_assoc,mul_comm,mul_left_comm] using H
  have hUcap : U ≤ 2*(n:ℝ)^(3/2:ℝ) := (fixedTruncation_bounds n (by omega)).2
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hproduct : (A:ℝ)*U ≤ ((X:ℝ)/2)^2 := by
    have hreserve : 8*(n:ℝ)^(a+3/2) ≤ (n:ℝ)^(2*c) :=
      power_reserve hnR (by norm_num)
        (hp.trans (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1/150:ℝ) ≤ 1/10)))
        (by linarith only [hUexp])
    have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hnP.le c) hcp 2
    rw [pow_two,← Real.rpow_add hnP,show c+c=2*c by ring] at hsq
    have hsq' : (n:ℝ)^(2*c) ≤ 4*(h:ℝ)^2 := by nlinarith only [hsq]
    calc
      _ ≤ (n:ℝ)^a*(2*(n:ℝ)^(3/2:ℝ)) :=
        mul_le_mul hAp hUcap hUpos.le (Real.rpow_nonneg hnP.le a)
      _ = 2*(n:ℝ)^(a+3/2) := by rw [← mul_assoc,mul_comm ((n:ℝ)^a) 2,mul_assoc,← Real.rpow_add hnP]
      _ ≤ (h:ℝ)^2 := by linarith only [hreserve,hsq']
      _ ≤ _ := pow_le_pow_left₀ hhP.le hhX' 2
  have hlog := Real.log_le_log (mul_pos hA0 hUpos) hproduct
  rw [Real.log_pow] at hlog
  have hloglow := Real.log_le_log (Real.rpow_pos_of_pos hnP (4/5:ℝ)) (hhlo.trans hhX')
  rw [Real.log_rpow hnP] at hloglow
  refine ⟨hA,hhN,hlow,hhX',hδ1,hδh.trans hhX',Nat.cast_le.mp hAX,
    hds ((X:ℝ)/2) (by linarith) (by linarith only [hXn',hXP]),
    hds X hXP hXn',?_,hloglow⟩
  simpa only [Nat.cast_ofNat,U,K,A] using hlog

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorGlobalSmoothingBudget.lean; sha256 e44553463f83b5df26eb41af89d20a628b84011427f7add597ff68f6acd0f9ef -/
section
/-! Global n-based delta and U give an explicit polynomial saving
for the prime-power and smoothed explicit-formula remainders. -/
open Filter
open scoped Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem globalSmoothingBudget
    {n X A h U a c D : ℝ}
    (hn : 3 ≤ n) (hX : 1 ≤ X) (hXn : X ≤ n)
    (hA1 : 1 ≤ A) (hh : 0 < h) (hD : 0 < D)
    (hAp : A ≤ n^a) (hcp : n^c ≤ 2*h)
    (hU : n^(3/2:ℝ) ≤ U)
    (hlog : Real.log (A*U) ≤ 2*Real.log n)
    (he₁ : a+2/3 ≤ c-1/10)
    (he₂ : a-1/6 ≤ c-1/10)
    (he₃ : 3*a-1/6 ≤ c-1/10)
    (he₄ : a+1/2 ≤ c-1/4) :
    let δ := n^(2/3:ℝ)
    let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        A^2*X^2*Real.log (A*U)/(δ*U))+
          2*Real.sqrt (3*X)*Real.log (3*X)
    A*E ≤ (8*D+16)*h*n^(-(1/10):ℝ)*Real.log n := by
  dsimp only
  let δ := n^(2/3:ℝ)
  let L := Real.log n
  let r := n^(-(1/10):ℝ)
  have hnP : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hA : 0 < A := by linarith
  have hδ : 0 < δ := Real.rpow_pos_of_pos hnP _
  have hr : 0 < r := Real.rpow_pos_of_pos hnP _
  have hU0 : 0 < U := (Real.rpow_pos_of_pos hnP _).trans_le hU
  have hL : 0 ≤ L := Real.log_nonneg hn1
  have hLX : Real.log X ≤ L := Real.log_le_log (by linarith) hXn
  have hLX0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hL3 : Real.log (3*X) ≤ 2*L := by
    have H := Real.log_le_log (by linarith : 0 < 3*X)
      (show 3*X ≤ n^2 by nlinarith only [hXn,hn,mul_le_mul_of_nonneg_right hn (show 0 ≤ n by positivity)])
    rw [Real.log_pow] at H
    norm_num at H
    exact H
  have hL30 : 0 ≤ Real.log (3*X) := Real.log_nonneg (by linarith)
  have hreserve (e : ℝ) (he : e ≤ c-1/10) : n^e ≤ 2*h*r := by
    calc
      _ ≤ n^(c-1/10) := Real.rpow_le_rpow_of_exponent_le hn1 he
      _ = n^c*r := by dsimp [r]; rw [← Real.rpow_add hnP]; congr 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcp hr.le
  have hroot : Real.sqrt X ≤ n^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hXn
  have hroot3 : Real.sqrt (3*X) ≤ 2*n^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    have hs : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg 3]
    exact mul_le_mul hs (Real.sqrt_le_sqrt hXn) (Real.sqrt_nonneg _) (by norm_num)
  have h1 : A*δ ≤ 2*h*r := by
    calc
      _ ≤ n^a*n^(2/3:ℝ) := mul_le_mul_of_nonneg_right hAp hδ.le
      _ = n^(a+2/3) := (Real.rpow_add hnP _ _).symm
      _ ≤ _ := hreserve _ he₁
  have h2 : A*Real.sqrt X/δ ≤ 2*h*r := by
    calc
      _ ≤ n^a*n^(1/2:ℝ)/δ :=
        div_le_div_of_nonneg_right
          (mul_le_mul hAp hroot (Real.sqrt_nonneg _) (Real.rpow_nonneg hnP.le _)) hδ.le
      _ = n^(a-1/6) := by
        dsimp [δ]
        rw [← Real.rpow_add hnP,← Real.rpow_sub hnP]
        congr 1 <;> ring
      _ ≤ _ := hreserve _ he₂
  have h3 : A^3*X^2/(δ*U) ≤ 2*h*r := by
    have hden : n^(2/3:ℝ)*n^(3/2:ℝ) ≤ δ*U :=
      mul_le_mul_of_nonneg_left hU hδ.le
    calc
      _ ≤ (n^a)^3*n^2/(n^(2/3:ℝ)*n^(3/2:ℝ)) := by
        apply le_trans (div_le_div_of_nonneg_right
          (mul_le_mul (pow_le_pow_left₀ hA.le hAp 3)
            (pow_le_pow_left₀ (by linarith) hXn 2) (sq_nonneg _) (by positivity))
          (mul_nonneg hδ.le hU0.le))
        exact div_le_div_of_nonneg_left (by positivity)
          (mul_pos (Real.rpow_pos_of_pos hnP _) (Real.rpow_pos_of_pos hnP _)) hden
      _ = n^(3*a-1/6) := by
        rw [← Real.rpow_add hnP,show (n^a)^3=n^(3*a) by
          rw [← Real.rpow_natCast,← Real.rpow_mul hnP.le]
          norm_num; congr 1 <;> ring,
          ← Real.rpow_natCast,← Real.rpow_add hnP,← Real.rpow_sub hnP]
        congr 1 <;> ring
      _ ≤ _ := hreserve _ he₃
  have h4 : A*Real.sqrt (3*X) ≤ 4*h*r := by
    calc
      _ ≤ n^a*(2*n^(1/2:ℝ)) :=
        mul_le_mul hAp hroot3 (Real.sqrt_nonneg _) (Real.rpow_nonneg hnP.le _)
      _ = 2*n^(a+1/2) := by rw [← mul_assoc,mul_comm (n^a) 2,mul_assoc,← Real.rpow_add hnP]
      _ ≤ 2*(2*h*r) := mul_le_mul_of_nonneg_left (hreserve _ (by linarith only [he₄])) (by norm_num)
      _ = _ := by ring
  have b1 := mul_le_mul h1 hLX hLX0 (by positivity : 0 ≤ 2*h*r)
  have b2 := mul_le_mul h2 hLX hLX0 (by positivity : 0 ≤ 2*h*r)
  have b3 := mul_le_mul h3 hlog
    (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hA1
      ((Real.one_le_rpow hn1 (by norm_num : (0:ℝ) ≤ 3/2)).trans hU)))
    (by positivity : 0 ≤ 2*h*r)
  have b4 := mul_le_mul h4 hL3 hL30 (by positivity : 0 ≤ 4*h*r)
  change A*(D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
      A^2*X^2*Real.log (A*U)/(δ*U))+
      2*Real.sqrt (3*X)*Real.log (3*X)) ≤ (8*D+16)*h*r*L
  have hsum :
      (A*δ)*Real.log X+(A*Real.sqrt X/δ)*Real.log X+
      (A^3*X^2/(δ*U))*Real.log (A*U) ≤ 8*h*r*L := by
    linarith only [b1,b2,b3]
  have H := mul_le_mul_of_nonneg_left hsum hD.le
  have H4 := mul_le_mul_of_nonneg_left b4 (show (0:ℝ) ≤ 2 by norm_num)
  convert add_le_add H H4 using 1 <;> ring

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorBlockScalarBudget.lean; sha256 8546a0b58def1ad72598c9fcbf1c535d9fb2d7bc069767ed08fe3288507b14ce -/
section
/-! Scalar assembly of the explicit-formula residual, good-zero energy
and principal energy. The only large parameter is the global logarithm L. -/
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem logDenominatorBudget {L l : ℝ} (hL : 0 < L) (hl : L/2 ≤ l) (k : ℕ) :
    1/l^k ≤ (2:ℝ)^k/L^k := by
  have hlp : 0 < l := by linarith
  apply (div_le_div_iff₀ (pow_pos hlp _) (pow_pos hL _)).2
  have hp : L^k ≤ (2*l)^k := pow_le_pow_left₀ hL.le (by linarith) _
  rw [mul_pow] at hp
  simpa only [one_mul] using hp

theorem blockScalarBudget {n X A h E K D C P L l₁ l₂ : ℝ}
    (hn : 1 ≤ n) (hX : 0 ≤ X) (hA : 0 ≤ A) (hh : 0 ≤ h)
    (hE : 0 ≤ E) (hK : 0 ≤ K) (hD : 0 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hL : 0 < L) (h₁ : L/2 ≤ l₁) (h₂ : L/2 ≤ l₂)
    (hk : K ≤ 5*L)
    (he : A*E ≤ (8*D+16)*h*n^(-(1/10):ℝ)*L)
    (hsmall : L^10 ≤ n^(1/5:ℝ)) :
    2*X*A^2*E^2 + 2*C*K^2*h^2*(X/2)/l₁^10 +
      2*C*K^2*h^2*X/l₂^10 + P*h^2*X/l₂^8 ≤
      (2*(8*D+16)^2+76800*C+256*P)*h^2*X/L^8 := by
  have hnP : 0 < n := by linarith
  have h₁p : 0 < l₁ := by linarith
  have h₂p : 0 < l₂ := by linarith
  have hp := pow_le_pow_left₀ (mul_nonneg hA hE) he 2
  have hr : (n^(-(1/10):ℝ))^2 = n^(-(1/5):ℝ) := by
    rw [pow_two,← Real.rpow_add hnP]
    congr 1 <;> ring
  have haux : n^(-(1/5):ℝ)*L^10 ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hnP.le (-(1/5):ℝ))
    rw [← Real.rpow_add hnP,show -(1/5:ℝ)+1/5=0 by ring,Real.rpow_zero] at H
    exact H
  have herror : (A*E)^2 ≤ (8*D+16)^2*h^2/L^8 := by
    apply (le_div_iff₀ (pow_pos hL _)).2
    calc
      _ ≤ ((8*D+16)*h*n^(-(1/10):ℝ)*L)^2*L^8 :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = ((8*D+16)^2*h^2)*(n^(-(1/5):ℝ)*L^10) := by
        simp only [mul_pow,hr]
        ring
      _ ≤ _ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left haux (show 0 ≤ (8*D+16)^2*h^2 by positivity)
  have hk' : K^2 ≤ 25*L^2 := by
    calc
      _ ≤ (5*L)^2 := pow_le_pow_left₀ hK hk 2
      _ = _ := by ring
  have hnorm (l : ℝ) (hl : L/2 ≤ l) :
      K^2/l^10 ≤ 25600/L^8 := by
    have hlp : 0 < l := by linarith
    have H := logDenominatorBudget hL hl 10
    norm_num at H
    calc
      _ ≤ (25*L^2)*(1024/L^10) := by
        rw [div_eq_mul_inv]
        apply mul_le_mul hk' _ (by positivity) (by positivity)
        simpa only [one_div] using H
      _ = _ := by field_simp; ring
  have hPden := logDenominatorBudget hL h₂ 8
  norm_num at hPden
  have t1 := mul_le_mul_of_nonneg_left herror (show 0 ≤ 2*X by positivity)
  have t2 := mul_le_mul_of_nonneg_left (hnorm l₁ h₁)
    (show 0 ≤ C*h^2*X by positivity)
  have t3 := mul_le_mul_of_nonneg_left (hnorm l₂ h₂)
    (show 0 ≤ 2*C*h^2*X by positivity)
  have t4 := mul_le_mul_of_nonneg_left hPden (show 0 ≤ P*h^2*X by positivity)
  convert add_le_add (add_le_add (add_le_add t1 t2) t3) t4 using 1 <;> ring

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorUniformBlockLogEight.lean; sha256 0422183f72777132c185ecb2d082030679e2b6e57937eff80034f184d205e248 -/
section
/-! Conditional uniform arithmetic block theorem. All scale choices
and logarithmic losses are explicit. The only unproved hypothesis is
DirichletUniformStrip σ, σ<1. -/
open Filter Finset OAI.Ostmann
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem uniformStrip_fixedBandBlockLogEight {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j < 10, ∀ X : ℕ,
      let A := fixedBandEnd n (j+1)
      let h := fixedBandWindow n j
      2*h ≤ X → X ≤ n →
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        M*(h:ℝ)^2*(X:ℝ)/(Real.log n)^8 := by
  obtain ⟨D,C,P,hD,hC,hP,X₀,hX₀,hbound⟩ :=
    actualPrimitiveBlockOfUniformStrip hσ hs 10
  let M := 2*(8*D+16)^2+76800*C+256*P
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbig : ∀ᶠ n : ℕ in atTop, X₀ ≤ (n:ℝ)^(4/5:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 4/5)).comp ht).eventually
      (eventually_ge_atTop X₀)
  filter_upwards [eventually_ge_atTop (4:ℕ),eventualFixedBandWindows,
    eventualFixedBandPowerEndpoints,eventualFixedBlockScale,hbig,
    GoldbachGRHBudget.eventually_log_pow_le 10 (1/5) 1 (by norm_num) (by norm_num)]
    with n hn hw hp hscale hbig hsmall
  intro j hj X
  dsimp only
  intro hhX hXn
  let A := fixedBandEnd n (j+1)
  let h := fixedBandWindow n j
  let K := fixedTruncationIndex n
  let δ := (n:ℝ)^(2/3:ℝ)
  let U := (2:ℝ)^(K+1)
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
  obtain ⟨hA,hh,hlow,hhX',hδ1,hδX,hAX,hds₁,hds₂,hlog,hloglow⟩ :=
    hscale j hj X hhX hXn
  obtain ⟨_,hAp,hcp⟩ := hp j hj
  obtain ⟨hhlo,_,_⟩ := hw j hj
  obtain ⟨_,_,_,_,_,he₁,he₂,he₃,he₄⟩ := fixedBandGlobalExponents j hj
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hX0' : X₀ ≤ (X:ℝ) := by
    have H := hbig.trans hhlo
    linarith only [H,hhX',hhR]
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hXn' : (X:ℝ) ≤ n := by exact_mod_cast hXn
  have hA1 : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hUlo : (n:ℝ)^(3/2:ℝ) ≤ U := (fixedTruncation_bounds n (by omega)).1
  have hU1 : 1 ≤ U :=
    (Real.one_le_rpow (by linarith : (1:ℝ) ≤ n) (by norm_num)).trans hUlo
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hLhalf : Real.log (n:ℝ)/2 ≤ Real.log ((X:ℝ)/2) := by linarith
  have hLhalfpos : 0 < (X:ℝ)/2 := by linarith only [hhR,hhX']
  have hLhalf_le : Real.log ((X:ℝ)/2) ≤ Real.log (n:ℝ) :=
    Real.log_le_log hLhalfpos (by linarith)
  have hLfull : Real.log (n:ℝ)/2 ≤ Real.log (X:ℝ) :=
    hLhalf.trans (Real.log_le_log hLhalfpos (by linarith))
  have hlog' : Real.log ((A:ℝ)*U) ≤ 2*Real.log n := by
    linarith only [hlog,hLhalf_le]
  have hLx : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg hX1
  have hL3 : 0 ≤ Real.log (3*(X:ℝ)) := Real.log_nonneg (by linarith)
  have hLAU : 0 ≤ Real.log ((A:ℝ)*U) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hA1 hU1)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have herror : (A:ℝ)*E ≤ (8*D+16)*(h:ℝ)*(n:ℝ)^(-(1/10):ℝ)*Real.log n :=
    globalSmoothingBudget hnR hX1 hXn' hA1 hhR hD hAp hcp hUlo hlog'
      he₁ he₂ he₃ he₄
  have hscalar := blockScalarBudget
    (show (1:ℝ) ≤ n by linarith) (Nat.cast_nonneg (α:=ℝ) X)
    (Nat.cast_nonneg (α:=ℝ) A) hhR.le hE
    (Nat.cast_nonneg (α:=ℝ) (K+1)) hD.le hC.le hP.le hL hLhalf hLfull
    (fixedTruncation_logBound n (by omega)) herror (by simpa only [one_mul] using hsmall)
  have H := hbound A X h K δ hA hX0' hh hlow hhX' hδ1 hδX hAX hds₁ hds₂ hlog
  dsimp only at H
  exact H.trans (by simpa only [M,E,δ,U,K,A,h] using hscalar)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorSignedSparsePacket.lean; sha256 ffc13794634561ec41ad24fcda9ffafb5c4ad2967d4c0e926183d94bd65765d7 -/
section
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

end

/-! BEGIN InnerFloorProductConductor.lean; sha256 42f48923c8bee33e34e0555986bd3707a43afef37e4f7fe18237040ff10602b5 -/
section
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

theorem divisorSum_le_log (m : ℕ) (hm : 0 < m) :
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
    (n : ℕ) (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt χ.conductor := by
  let d := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hdp
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hmp
  have hqR : (q:ℝ)=(d:ℝ)*(m:ℝ) := by exact_mod_cast hm
  have hsub : n.divisors.filter (fun f => d*f ∣ q) ⊆ m.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left hdp hdiv,hmp.ne'⟩
  have hmq : m ≤ q := by
    rw [hm]
    exact Nat.le_mul_of_pos_left _ hdp
  have hlog : Real.log m≤Real.log q :=
    Real.log_le_log hmR (by exact_mod_cast hmq)
  have hs : (Real.sqrt (d:ℝ))^2=(d:ℝ) := Real.sq_sqrt hdR.le
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 hdR
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f ∣ q),(f:ℝ)) :=
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
      calc
        _ = (Real.sqrt (d:ℝ))^2 * ((m:ℝ)*(1+Real.log q)) := by ring
        _ = (d:ℝ)*((m:ℝ)*(1+Real.log q)) := by rw [hs]
        _ = _ := by rw [hqR]; ring

/-- The high-product-conductor part of the signed quadratic form has a
uniform square-root saving, independent of gcd(n,q). -/
theorem highProductConductorPacketBound
    (n : ℕ) (hn : 0 < n) (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) (hD : 0 < D) :
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

end

/-! BEGIN InnerFloorProductFamily.lean; sha256 f03dc1f3a8d78662c696e46e04d34af491645f58b0a6bb8dca16b52780d6d1d4 -/
section
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

end

/-! BEGIN InnerFloorBoundaryEnergy.lean; sha256 fd93dd2c99866510f6f2eeb1d38654034f27945644496fe4bae574e45cf37b09 -/
section
/-!
Uniform energy of a clipped interval, with no prime distribution input.
The centered model term costs only reciprocal totients. This is used
on boundary windows of length at most h rather than on the full bulk.
-/
open Finset BombieriVinogradov.LargeSieve InnerFloorLinearTotient
open GoldbachGRHWindow (additiveModel)
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem additiveIntervalFamilyEnergy (A N : ℕ) (M : ℤ)
    (a : ℤ → ℂ) (hA : 0 < A) (W : ℝ) (hW : 0 ≤ W)
    (ha : ∀ k∈range N, ‖shiftedIntervalCoefficients a M k‖ ≤ W) :
    (∑ q∈Icc 1 A,modulusAdditiveEnergy a M N q) ≤
      64*((N:ℝ)+(A:ℝ)^2)*(N:ℝ)*W^2 := by
  rw [sum_modulusAdditiveEnergy_eq_fareySamples]
  apply (additiveLargeSieve hA (shiftedIntervalCoefficients a M)).trans
  have hs : (∑ k∈range N, ‖shiftedIntervalCoefficients a M k‖^2) ≤
      (N:ℝ)*W^2 := by
    calc
      _ ≤ ∑ _k∈range N,W^2 :=
        sum_le_sum fun k hk => pow_le_pow_left₀ (norm_nonneg _) (ha k hk) 2
      _ = _ := by simp [nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

theorem sum_unitModelEnergy (q : ℕ) [NeZero q] :
    (∑ u : (ZMod q)ˣ, ‖additiveModel q (u:ZMod q)‖^2) ≤
      1/(q.totient:ℝ) := by
  have hφ : 0 < (q.totient:ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hterm (u : (ZMod q)ˣ) : ‖additiveModel q (u:ZMod q)‖ ≤
      1/(q.totient:ℝ) := by
    rw [GoldbachGRHWindow.additiveModel_eq_moebius _ u.isUnit,norm_div,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (DyadicMixedB4MoebiusGauss.norm_moebiusComplex_le_one q)
      hφ.le
  calc
    _ ≤ ∑ _u : (ZMod q)ˣ, (1/(q.totient:ℝ))^2 :=
      sum_le_sum fun u _ => pow_le_pow_left₀ (norm_nonneg _) (hterm u) 2
    _ = _ := by
      rw [sum_const,nsmul_eq_mul,card_univ,ZMod.card_units_eq_totient]
      field_simp

def centeredIntervalEnergy (a : ℤ → ℂ) (M : ℤ) (N q : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u -
      (N:ℂ)*additiveModel q (u:ZMod q)‖^2

theorem centeredIntervalEnergy_le (a : ℤ → ℂ) (M : ℤ) (N q : ℕ)
    (hq : 0 < q) :
    centeredIntervalEnergy a M N q ≤
      2*modulusAdditiveEnergy a M N q+2*(N:ℝ)^2/(q.totient:ℝ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [modulusAdditiveEnergy_eq]
  simp only [centeredIntervalEnergy,dif_neg hq.ne']
  have hterm (u : (ZMod q)ˣ) :
      ‖intervalAdditiveResidueSum a M N q u -
        (N:ℂ)*additiveModel q (u:ZMod q)‖^2 ≤
        2*‖intervalAdditiveResidueSum a M N q u‖^2+
        2*(N:ℝ)^2*‖additiveModel q (u:ZMod q)‖^2 := by
    have hs := norm_sub_le (intervalAdditiveResidueSum a M N q u)
      ((N:ℂ)*additiveModel q (u:ZMod q))
    rw [norm_mul,Complex.norm_natCast] at hs
    exact (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans
      (by
        have H := sq_nonneg (‖intervalAdditiveResidueSum a M N q u‖ -
          (N:ℝ)*‖additiveModel q (u:ZMod q)‖)
        nlinarith only [H])
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, (2*‖intervalAdditiveResidueSum a M N q u‖^2+
        2*(N:ℝ)^2*‖additiveModel q (u:ZMod q)‖^2) := sum_le_sum fun u _ => hterm u
    _ = 2*(∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖^2)+
        2*(N:ℝ)^2*(∑ u : (ZMod q)ˣ, ‖additiveModel q (u:ZMod q)‖^2) := by
      rw [sum_add_distrib,← mul_sum,← mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_unitModelEnergy q)
        (show (0:ℝ) ≤ 2*(N:ℝ)^2 from by positivity)
      calc
        _ ≤ 2*(∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖^2)+
            2*(N:ℝ)^2*(1/(q.totient:ℝ)) := add_le_add le_rfl h
        _ = _ := by
          simp only [div_eq_mul_inv,one_mul]
          congr 1
          congr 1
          apply sum_congr
          · ext u
            simp
          · intro u _
            rfl
          all_goals simp only [one_mul]

/-- For any interval of N terms, the total centered reduced numerator
energy has at most a quadratic logarithmic model cost. -/
theorem centeredIntervalFamilyEnergy (A N : ℕ) (M : ℤ)
    (a : ℤ → ℂ) (hA : 0 < A) (W : ℝ) (hW : 0 ≤ W)
    (ha : ∀ k∈range N, ‖shiftedIntervalCoefficients a M k‖ ≤ W) :
    (∑ q∈Icc 1 A,centeredIntervalEnergy a M N q) ≤
      128*((N:ℝ)+(A:ℝ)^2)*(N:ℝ)*W^2+
      2*(N:ℝ)^2*(weightConstant*(1+Real.log A))^2 := by
  have hr := commonMultipleTotientWeight A 1 (by decide) hA
  simp only [one_dvd,filter_true,Nat.cast_one] at hr
  calc
    _ ≤ ∑ q∈Icc 1 A, (2*modulusAdditiveEnergy a M N q+2*(N:ℝ)^2/(q.totient:ℝ)) :=
      sum_le_sum fun q hq => centeredIntervalEnergy_le a M N q (mem_Icc.mp hq).1
    _ = 2*(∑ q∈Icc 1 A,modulusAdditiveEnergy a M N q)+
      2*(N:ℝ)^2*(∑ q∈Icc 1 A,1/(q.totient:ℝ)) := by
      rw [sum_add_distrib,← mul_sum]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left
        (additiveIntervalFamilyEnergy A N M a hA W hW ha) (by norm_num : (0:ℝ)≤2)
      have h2 := mul_le_mul_of_nonneg_left hr (by positivity : 0≤2*(N:ℝ)^2)
      linarith only [h1,h2]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorGeometry.lean; sha256 98b89eceb61c72064eefbe955b847da8b66c3d6c5995347341a1f2977e28a2d2 -/
section
/- Geometry reduction only; this file does not claim the published asymptotic estimate. -/
namespace InnerFloorResearch

def arcSet (B : ℕ) (r n : ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ r / ((q : ℝ) * n)}

theorem arcSet_mono {B C : ℕ} {r s n : ℝ}
    (hB : B ≤ C) (hr : r ≤ s) (hn : 0 ≤ n) :
    arcSet B r n ⊆ arcSet C s n := by
  intro t ht
  obtain ⟨q,a,hq,hqb,ha,hcop,hclose⟩ := ht
  exact ⟨q,a,hq,hqb.trans hB,ha,hcop,hclose.trans
    (div_le_div_of_nonneg_right hr (mul_nonneg (Nat.cast_nonneg q) hn))⟩

theorem inner_remainder_eq (Q B : ℕ) (r R u n : ℝ)
    (hr : r ≤ R) (hu : u ≤ R) (hn : 0 ≤ n) :
    (((arcSet B R n \ arcSet Q r n) \
      (arcSet Q R n \ arcSet Q r n)) ∩ arcSet B u n) =
      arcSet B u n \ arcSet Q R n := by
  have hA := arcSet_mono (B := Q) (C := Q) (r := r) (s := R) le_rfl hr hn
  have hI := arcSet_mono (B := B) (C := B) (r := u) (s := R) le_rfl hu hn
  ext t
  constructor
  · rintro ⟨⟨⟨hw,ha⟩,hl⟩,hi⟩
    exact ⟨hi,fun h => hl ⟨h,ha⟩⟩
  · rintro ⟨hi,hl⟩
    have ha : t ∉ arcSet Q r n := fun h => hl (hA h)
    exact ⟨⟨⟨hI hi,ha⟩,fun h => hl h.1⟩,hi⟩

theorem medium_witness (Q B : ℕ) (u R n : ℝ)
    (hu : u ≤ R) (hn : 0 ≤ n) {t : ℝ}
    (ht : t ∈ arcSet B u n \ arcSet Q R n) :
    ∃ q a : ℕ, Q < q ∧ 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ u / ((q : ℝ) * n) := by
  obtain ⟨hi,hl⟩ := ht
  obtain ⟨q,a,hq,hqb,ha,hcop,hclose⟩ := hi
  have hlarge : Q < q := by
    by_contra! hsmall
    apply hl
    exact ⟨q,a,hq,hsmall,ha,hcop,hclose.trans
      (div_le_div_of_nonneg_right hu (mul_nonneg (Nat.cast_nonneg q) hn))⟩
  exact ⟨q,a,hlarge,hq,hqb,ha,hcop,hclose⟩


/-- Separation for two reduced rational windows with independently specified widths.
The cross-multiplication argument adapts MajorNumeratorDilation's
cross_eq_of_overlap (Apache-2.0; original separation credited to wzhxzkk, PR 153). -/
theorem overlap_center_eq {q r a b : ℕ} {u v n t : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hn : 0 < n)
    (hc : a.Coprime q) (hd : b.Coprime r)
    (hsmall : u*(r:ℝ)+v*(q:ℝ)<n)
    (ha : |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n))
    (hb : |t-(b:ℝ)/r| ≤ v/((r:ℝ)*n)) :
    q=r ∧ a=b := by
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hprod : 0 < (q:ℝ)*r := mul_pos hqr hrr
  have hrad : u/((q:ℝ)*n)+v/((r:ℝ)*n)<1/((q:ℝ)*r) := by
    calc
      _ = (u*(r:ℝ)+v*(q:ℝ))/((q:ℝ)*r*n) := by
        field_simp
      _ < n/((q:ℝ)*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).2 hsmall
      _ = _ := by field_simp
  have he : a*r=b*q := by
    by_contra hne
    have hsep : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp,
        abs_div, abs_of_pos hprod]
      apply (div_le_div_iff_of_pos_right hprod).2
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r-b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r-b*q)]
    have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at ht
    linarith
  have hdiv1 : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv2 : r ∣ q := hd.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv1 hdiv2
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

def mediumBand (Q B : ℕ) (u n : ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, Q<q ∧ 1≤q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n)}

/-- The excluded low-modulus mask can be dropped exactly once the rational
separation inequality holds. This statement makes no estimate of prime sums. -/
theorem masked_medium_eq (Q B : ℕ) (u R n : ℝ)
    (hu : 0≤u) (huR : u≤R) (hn : 0<n)
    (hsmall : u*(Q:ℝ)+R*(B:ℝ)<n) :
    arcSet B u n \ arcSet Q R n = mediumBand Q B u n := by
  ext t
  constructor
  · exact fun ht => medium_witness Q B u R n huR hn.le ht
  · rintro ⟨q,a,hqQ,hq,hqB,ha,hcop,hclose⟩
    refine ⟨⟨q,a,hq,hqB,ha,hcop,hclose⟩,?_⟩
    rintro ⟨r,b,hr,hrQ,hb,hd,hnear⟩
    have hsmall' : u*(r:ℝ)+R*(q:ℝ)<n :=
      (add_le_add
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hrQ) hu)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hqB) (hu.trans huR))).trans_lt hsmall
    have he := overlap_center_eq (by omega : 0<q) (by omega : 0<r)
      hn hcop hd hsmall' hclose hnear
    omega

theorem mediumBand_unique (Q B : ℕ) (u n : ℝ) (hu : 0≤u) (hn : 0<n)
    (hsmall : 2*u*(B:ℝ)<n)
    {q r a b : ℕ} {t : ℝ}
    (hq : Q<q) (hr : Q<r) (hqB : q≤B) (hrB : r≤B)
    (hc : a.Coprime q) (hd : b.Coprime r)
    (ha : |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n))
    (hb : |t-(b:ℝ)/r| ≤ u/((r:ℝ)*n)) :
    q=r ∧ a=b := by
  apply overlap_center_eq (by omega : 0<q) (by omega : 0<r) hn hc hd _ ha hb
  have h1 := mul_le_mul_of_nonneg_left (show (q:ℝ)≤B by exact_mod_cast hqB) hu
  have h2 := mul_le_mul_of_nonneg_left (show (r:ℝ)≤B by exact_mod_cast hrB) hu
  linarith

end InnerFloorResearch

end

/-! BEGIN InnerFloorModelTransfer.lean; sha256 d527e1221bbcc5f08a101c5dde1dd1d5616138c7b5d2d6997f32c38c9ebae91a -/
section
open Finset MeasureTheory Filter
open scoped Interval Topology Classical

namespace InnerFloorResearch

noncomputable section
set_option maxHeartbeats 1500000

open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHArcs (center centers mem_centers)
open GoldbachGRHApproximation (integrand)
open GoldbachGRHModel (model model_continuous)

def realRadius (n : ℕ) (u : ℝ) (q : ℕ) : ℝ := u / ((q : ℝ) * (n : ℝ))

def realArc (n : ℕ) (u : ℝ) (i : ℕ × ℕ) : Set ℝ :=
  {t | |t - center i| ≤ realRadius n u i.1}

theorem realArc_eq_Icc (n : ℕ) (u : ℝ) (i : ℕ × ℕ) :
    realArc n u i =
      Set.Icc (center i - realRadius n u i.1) (center i + realRadius n u i.1) := by
  ext t
  change |t - center i| ≤ _ ↔ _
  rw [abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

def mediumIndices (Q A : ℕ) : Finset (ℕ × ℕ) :=
  (centers A).filter (fun i => Q < i.1)

theorem mediumIndices_spec {Q A : ℕ} {i : ℕ × ℕ} :
    i ∈ mediumIndices Q A ↔ Q < i.1 ∧ i.1 ≤ A ∧ i.2 ≤ i.1 ∧ i.2.Coprime i.1 := by
  simp only [mediumIndices, mem_filter, mem_centers]
  constructor
  · rintro ⟨⟨_, hA, ha, hc⟩, hQ⟩
    exact ⟨hQ, hA, ha, hc⟩
  · rintro ⟨hQ, hA, ha, hc⟩
    exact ⟨⟨by omega, hA, ha, hc⟩, hQ⟩

theorem mediumBand_eq_union (n Q A : ℕ) (u : ℝ) :
    mediumBand Q A u n = ⋃ i ∈ mediumIndices Q A, realArc n u i := by
  ext t
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨q,a,hQ,_,hA,ha,hc,ht⟩
    exact ⟨(q,a), mediumIndices_spec.mpr ⟨hQ,hA,ha,hc⟩, ht⟩
  · rintro ⟨⟨q,a⟩,hi,ht⟩
    obtain ⟨hQ,hA,ha,hc⟩ := mediumIndices_spec.mp hi
    exact ⟨q,a,hQ,by omega,hA,ha,hc,ht⟩

theorem measurable_mediumBand (n Q A : ℕ) (u : ℝ) :
    MeasurableSet (mediumBand Q A u n) := by
  rw [mediumBand_eq_union]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => by
    rw [realArc_eq_Icc]
    exact measurableSet_Icc

def arcCell (n : ℕ) (u : ℝ) (i : ℕ × ℕ) : Set ℝ := realArc n u i ∩ Set.Ioc 0 1

theorem measurable_arcCell (n : ℕ) (u : ℝ) (i : ℕ × ℕ) :
    MeasurableSet (arcCell n u i) := by
  unfold arcCell
  rw [realArc_eq_Icc]
  exact measurableSet_Icc.inter measurableSet_Ioc

theorem arcCells_disjoint {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) :
    (↑(mediumIndices Q A) : Set (ℕ × ℕ)).PairwiseDisjoint (arcCell n u) := by
  rintro ⟨q,a⟩ hi ⟨r,b⟩ hj hij
  change Disjoint (arcCell n u (q,a)) (arcCell n u (r,b))
  rw [Set.disjoint_left]
  intro t ht ht'
  obtain ⟨hq,hqA,_,hc⟩ := mediumIndices_spec.mp (show (q,a) ∈ mediumIndices Q A from hi)
  obtain ⟨hr,hrA,_,hd⟩ := mediumIndices_spec.mp (show (r,b) ∈ mediumIndices Q A from hj)
  obtain ⟨hqr,hab⟩ := mediumBand_unique Q A u (n : ℝ) hu (by exact_mod_cast hn)
    hsep hq hr hqA hrA hc hd ht.1 ht'.1
  exact hij (Prod.ext hqr hab)

/-- Interior centers yield the full symmetric beta-window. The singleton
at zero does not contribute to the integral. -/
theorem arcCell_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n q a : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u) (hun : u ≤ n)
    (hq : 2 ≤ q) (ha : a ≤ q) (hc : a.Coprime q) (G : ℝ → E) :
    (∫ t in arcCell n u (q,a), G (t - center (q,a))) =
      ∫ t in -(realRadius n u q)..(realRadius n u q), G t := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha0 : 1 ≤ a := by
    by_contra! h
    have he : a = 0 := by omega
    have h1 := (Nat.coprime_zero_left q).mp (he ▸ hc)
    omega
  have haq : a + 1 ≤ q := by
    by_contra! h
    have he : a = q := by omega
    have h1 : q = 1 := by simpa [he, Nat.Coprime] using hc
    omega
  have hrad : 0 ≤ realRadius n u q := div_nonneg hu (mul_pos hqR hnR).le
  have hr : realRadius n u q ≤ 1/(q : ℝ) := by
    apply (div_le_iff₀ (mul_pos hqR hnR)).2
    convert hun using 1
    field_simp
  have hleft : realRadius n u q ≤ center (q,a) :=
    hr.trans (div_le_div_of_nonneg_right (by exact_mod_cast ha0) hqR.le)
  have hright : center (q,a) + realRadius n u q ≤ 1 := by
    apply (add_le_add_right hr _).trans
    change (a : ℝ)/q + 1/(q : ℝ) ≤ 1
    rw [← add_div, div_le_one hqR]
    exact_mod_cast haq
  have hsub : realArc n u (q,a) ⊆ Set.Icc 0 1 := by
    rw [realArc_eq_Icc]
    exact Set.Icc_subset_Icc (sub_nonneg.mpr hleft) hright
  have he : arcCell n u (q,a) =ᵐ[volume] realArc n u (q,a) := by
    have h : Set.Ioc (0 : ℝ) 1 =ᵐ[volume] Set.Icc (0 : ℝ) 1 := Ioc_ae_eq_Icc
    filter_upwards [h] with t ht
    change (t ∈ realArc n u (q,a) ∧ t ∈ Set.Ioc 0 1) ↔ t ∈ realArc n u (q,a)
    exact ⟨And.left, fun hp => ⟨hp, ht.mpr (hsub hp)⟩⟩
  have hInt :
      (∫ t in arcCell n u (q,a), G (t - center (q,a))) =
        ∫ t in realArc n u (q,a), G (t - center (q,a)) :=
    setIntegral_congr_set he
  rw [hInt,
    realArc_eq_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hrad] :
      center (q,a) - realRadius n u q ≤ center (q,a) + realRadius n u q),
    intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

theorem sum_mediumIndices {E : Type*} [AddCommMonoid E] (Q A : ℕ)
    (F : ℕ × ℕ → E) :
    (∑ i ∈ mediumIndices Q A, F i) =
      ∑ q ∈ Ioc Q A, ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), F (q,a) := by
  have he : (Icc 1 A).filter (fun q => Q < q) = Ioc Q A := by
    ext q
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [mediumIndices, sum_filter, GoldbachGRHArcs.sum_centers_eq, ← he]
  conv_rhs => rw [sum_filter]
  apply sum_congr rfl
  intro q hq
  by_cases h : Q < q <;> simp [h]

def mediumIntegral (n Q A : ℕ) (u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (mediumBand Q A u n).indicator (integrand n) t

def mediumModel (n Q A : ℕ) (u : ℝ) : ℂ :=
  ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, model n i t ^ 2 * phase (-(n : ℝ)*t)

def mediumCellEnergy (n Q A : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, ‖primeSum n t - model n i t‖^2

theorem mediumIntegral_eq_sum {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) :
    mediumIntegral n Q A u = ∑ i ∈ mediumIndices Q A, ∫ t in arcCell n u i, integrand n t := by
  have hf : Continuous (integrand n) := by unfold integrand primeSum phase; fun_prop
  have hUnion :
      (⋃ i ∈ mediumIndices Q A, arcCell n u i) =
        mediumBand Q A u n ∩ Set.Ioc 0 1 := by
    ext t
    rw [mediumBand_eq_union]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, arcCell]
    constructor
    · rintro ⟨i, hi, ha, ht⟩
      exact ⟨⟨i,hi,ha⟩,ht⟩
    · rintro ⟨⟨i,hi,ha⟩,ht⟩
      exact ⟨i,hi,ha,ht⟩
  rw [mediumIntegral, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator (measurable_mediumBand n Q A u), Set.inter_comm (Set.Ioc 0 1) (mediumBand Q A u n), ← hUnion]
  exact integral_biUnion_finset (mediumIndices Q A) (fun i _ => measurable_arcCell n u i)
    (arcCells_disjoint hn hu hsep) (fun i _ => (hf.intervalIntegrable 0 1).1.mono_set
      Set.inter_subset_right)

theorem mediumModel_re {n Q A : ℕ} {u : ℝ} (hn : 0 < n) (hQ : 1 ≤ Q)
    (hu : 0 ≤ u) (hun : u ≤ (n : ℝ)) :
    (mediumModel n Q A u).re =
      ∑ q ∈ Ioc Q A, (GoldbachExplicitModeledMajor.coefficient q n).re *
        GoldbachGRHKernel.mass n (realRadius n u q) := by
  have he :
      mediumModel n Q A u =
        ∑ q ∈ Ioc Q A, GoldbachExplicitModeledMajor.coefficient q n *
          (GoldbachGRHKernel.mass n (realRadius n u q) : ℂ) := by
    rw [mediumModel, sum_mediumIndices]
    apply sum_congr rfl
    intro q hq
    have hq₂ : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
    have hR : ((range (q+1)).filter (fun a => a.Coprime q)) =
        (range q).filter (fun a => a.Coprime q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨ha,hc⟩
        have hne : a ≠ q := by
          intro heq
          have h1 : q = 1 := by simpa [heq,Nat.Coprime] using hc
          omega
        exact ⟨by omega,hc⟩
      · rintro ⟨ha,hc⟩
        exact ⟨by omega,hc⟩
    rw [hR, ← GoldbachGRHModelAssembly.sum_signedFactor, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨haq,hcop⟩ := mem_filter.mp ha
    simp_rw [GoldbachGRHModelAssembly.model_square_eq]
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal,
      arcCell_translate hn hu hun hq₂ (mem_range.mp haq).le hcop
        (fun t : ℝ => ‖GoldbachGRHKernel.kernel n t‖^2)] <;> rfl
  rw [he]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-- The Ramanujan model has the required signed lower floor at arbitrary
real widths up to half the ambient length. The weights are kernel masses
on nested beta-intervals, so the prefix bound is used by summation by parts. -/
theorem realWidthModelFloor (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n Q A : ℕ, 0 < n → Even n → 1 ≤ Q → K ≤ Q → Q ≤ A →
      ∀ u : ℝ, 0 < u → 2*u ≤ (n : ℝ) →
        -(ε*(n : ℝ)) ≤ (mediumModel n Q A u).re := by
  obtain ⟨K,hK⟩ := GoldbachGRHSignedModel.harmonic_suffix_floor (ε/2) (by positivity)
  refine ⟨K, ?_⟩
  intro n Q A hn he hQ hstart hQA u hu hun
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let w (q : ℕ) := GoldbachGRHKernel.mass n (realRadius n u q)
  have hpos (q : ℕ) (hq : Q ≤ q) : 0 < realRadius n u q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hQ.trans hq
    unfold realRadius
    exact div_pos hu (mul_pos (by linarith) hnR)
  have hmono (q : ℕ) (hq : Q ≤ q) : w (q+1) ≤ w q := by
    apply GoldbachGRHKernel.mass_mono n (hpos (q+1) (by omega)).le
    have hqR : (0 : ℝ) < q := by exact_mod_cast hQ.trans hq
    unfold realRadius
    exact div_le_div_of_nonneg_left hu.le (mul_pos hqR hnR) (by
      push_cast
      nlinarith only [hnR])
  have hw (q : ℕ) (hq : Q ≤ q) : 0 ≤ w q :=
    GoldbachGRHKernel.mass_nonneg n (hpos q hq).le
  have hr : realRadius n u Q ≤ 1/2 := by
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    apply (div_le_iff₀ (by positivity : 0 < (Q : ℝ)*(n : ℝ))).2
    nlinarith only [hun, mul_le_mul_of_nonneg_right hQR hnR.le]
  have hwQ : w Q ≤ (n : ℝ)+1 :=
    sub_nonneg.mp (GoldbachGRHKernel.mass_loss n (hpos Q le_rfl) hr).1
  have hweight := BandTail.weighted_prefix_lower Q A
    (fun q => (GoldbachExplicitModeledMajor.coefficient q n).re) w
    (ε/2) hQA (by positivity) hw hmono (by
      intro i hi _
      have hh := hK Q hstart n i he hi
      refine hh.trans (le_of_eq (sum_congr rfl ?_))
      intro q hq
      exact (GoldbachGRHSignedModel.coefficient_re_eq n q
        ((Nat.zero_le Q).trans_lt (mem_Ioc.mp hq).1)).symm)
  rw [mediumModel_re hn hQ hu.le (by linarith)]
  change -(ε*(n : ℝ)) ≤ ∑ q ∈ Ioc Q A, _ * w q
  apply le_trans _ hweight
  apply neg_le_neg
  calc
    _ ≤ (ε/2)*((n : ℝ)+1) := mul_le_mul_of_nonneg_left hwQ (by positivity)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hn1 hε.le]

/-- The finite Fourier reduction with real width and the exact denominator
band. The modulus factor is in `GBSkirtVariance.mass`. -/
theorem middleEnergy_of_window {n Q A h : ℕ} {u : ℝ} (hn : 0 < n)
    (hQ : 1 ≤ Q) (hh : 0 < h) (hu : 0 ≤ u) (hun : u ≤ n)
    (hwidth : 6*(h : ℝ)*u ≤ n) :
    (h : ℝ)^2 * mediumCellEnergy n Q A u ≤
      8 * ∑ q ∈ Ioc Q A, GBSkirtVariance.mass q n h := by
  rw [mediumCellEnergy, sum_mediumIndices]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply sum_le_sum
  intro q hq
  have hq₂ : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
  have hq0 : 0 < q := by omega
  letI : NeZero q := ⟨hq0.ne'⟩
  let δ := realRadius n u q
  let E (a : ZMod q) : ℝ := ∫ β in -δ..δ,
    ‖GoldbachWindow.poly (n+1) (GoldbachGRHAnalytic.errorCoeff a) β‖^2
  have hd : 0 ≤ δ := by unfold δ realRadius; positivity
  have hw : 6*(h : ℝ)*δ ≤ 1 := by
    have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq0
    unfold δ realRadius
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (q : ℝ)*(n : ℝ)), one_mul]
    exact hwidth.trans (by nlinarith only [mul_le_mul_of_nonneg_left hqR (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hE (a : ZMod q) : 0 ≤ E a :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hc (a : ℕ) (ha : a ∈ (range (q+1)).filter (fun a => a.Coprime q)) :
      (∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) = E (a : ZMod q) := by
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    have hUnit := (ZMod.isUnit_iff_coprime a q).2 hcop
    let G (β : ℝ) := ‖GoldbachWindow.poly (n+1)
      (GoldbachGRHAnalytic.errorCoeff (a : ZMod q)) β‖^2
    have he (t : ℝ) : G (t - center (q,a)) = ‖primeSum n t - model n (q,a) t‖^2 := by
      unfold G
      rw [GoldbachGRHAnalytic.shifted_error_eq, GoldbachGRHWindow.additiveModel_eq_moebius _ hUnit]
      unfold model
      rw [show (a : ℝ)/q+(t-center (q,a)) = t by unfold center; ring]
    calc
      _ = ∫ t in arcCell n u (q,a), G (t - center (q,a)) := by simp_rw [he]
      _ = E (a : ZMod q) :=
        arcCell_translate hn hu hun hq₂ (Nat.lt_succ_iff.mp (mem_range.mp haq)) hcop G
  have hcells :
      (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
        ∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) ≤
        2 * ∑ a : ZMod q, E a :=
    (le_of_eq (sum_congr rfl hc)).trans (GoldbachGRHArcs.sum_numerators_le_real q E hE)
  have hden := GBSkirtVariance.denominator_bound (q := q) n h δ hh hd hw
  change (h : ℝ)^2/4 * (∑ a : ZMod q, E a) ≤ _ at hden
  rw [GBSkirtVariance.mass, dite_eq_right hq0.ne']
  linarith only [mul_le_mul_of_nonneg_left hcells (sq_nonneg (h : ℝ)), hden]

theorem signedMediumDifference {n Q A : ℕ} {u η : ℝ} (hn : 2 ≤ n) (hu : 0 ≤ u)
    (hsep : 2*u*(A : ℝ) < (n : ℝ)) (hη : 0 < η) :
    ‖mediumIntegral n Q A u - mediumModel n Q A u‖ ≤
      (1+1/η)*mediumCellEnergy n Q A u + η*((n : ℝ)+1)*(Real.log (n : ℝ))^2 := by
  let osc (t : ℝ) := phase (-(n : ℝ)*t)
  have hosc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
  rw [mediumIntegral_eq_sum (by omega) hu hsep, mediumModel, ← sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in arcCell n u i, integrand n t) -
        (∫ t in arcCell n u i, model n i t ^ 2 * osc t) =
      ∫ t in arcCell n u i, (primeSum n t ^ 2 - model n i t ^ 2) * osc t := by
    have hpart : arcCell n u i ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_right
    have h₁ : IntegrableOn (integrand n) (arcCell n u i) volume :=
      (((hS.pow 2).mul hosc).intervalIntegrable 0 1).1.mono_set hpart
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t) (arcCell n u i) volume :=
      ((((model_continuous n i).pow 2).mul hosc).intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [integrand, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  have hb := GoldbachGRHWindowEnergy.sum_setIntegral_square_difference_le
    (mediumIndices Q A) (arcCell n u) (fun i _ => measurable_arcCell n u i)
    (fun _ _ => Set.inter_subset_right) (arcCells_disjoint (by omega) hu hsep)
    (primeSum n) (model n) osc hS (fun i _ => model_continuous n i) hosc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(n : ℝ)*t)))) hη
  exact hb.trans (by
    unfold mediumCellEnergy
    rw [mul_assoc η]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (GoldbachGRHAnalytic.prime_sum_energy_le n hn) hη.le) _)

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorReducedModelTransfer.lean; sha256 074751e694b8e3e4dbf7fabbefb9eaa6db74dff7a0b8bd53a410e0b27cf1fc6e -/
section
/-!
Exact reduced-numerator bridge for real-width model error. Allows an
independent window for each denominator band: 6 h u <= Q n.
The unit/numerator bijection is adapted from accepted
ShortProgressionsMeanTheta (XBribo #3789, pinned upstream 1fe24b28).
No analytic input is assumed beyond the already verified Gallagher
inequality. This replaces the earlier all-residue variance bound.
-/
open Finset MeasureTheory
open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHArcs (center)
open GoldbachGRHModel (model)
open scoped Classical Interval
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem inner_sum_units_eq_sum_coprime (q : ℕ) [NeZero q]
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ a : (ZMod q)ˣ, f ((a : ZMod q).val)) =
      ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), f a := by
  refine Finset.sum_bij (fun (a : (ZMod q)ˣ) _ => (a : ZMod q).val) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ hab
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (a : ZMod q), ← ZMod.natCast_zmod_val (b : ZMod q), hab]
  · intro a ha
    obtain ⟨haq, hac⟩ := Finset.mem_filter.mp ha
    have hu := (ZMod.isUnit_iff_coprime a q).mpr hac
    exact ⟨hu.unit, Finset.mem_univ _, by
      rw [hu.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp haq)]⟩
  · intro a _
    rfl

theorem middleEnergy_of_reducedWindow {n Q A h : ℕ} {u : ℝ} (hn : 0 < n)
    (hQ : 1 ≤ Q) (hh : 0 < h) (hu : 0 ≤ u) (hun : u ≤ n)
    (hwidth : 6*(h : ℝ)*u ≤ (Q:ℝ)*n) :
    (h : ℝ)^2 * mediumCellEnergy n Q A u ≤
      4 * ∑ q ∈ Ioc Q A, ∑ m∈range (n+1+h), reducedMovingLevelEnergy q n h m := by
  rw [mediumCellEnergy, sum_mediumIndices]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply sum_le_sum
  intro q hq
  have hq₂ : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
  have hq0 : 0 < q := by omega
  letI : NeZero q := ⟨hq0.ne'⟩
  let δ := realRadius n u q
  let E (a : ZMod q) : ℝ := ∫ β in -δ..δ,
    ‖GoldbachWindow.poly (n+1) (GoldbachGRHAnalytic.errorCoeff a) β‖^2
  have hd : 0 ≤ δ := by unfold δ realRadius; positivity
  have hw : 6*(h : ℝ)*δ ≤ 1 := by
    have hqR : (Q:ℝ) ≤ q := by exact_mod_cast (mem_Ioc.mp hq).1.le
    unfold δ realRadius
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (q : ℝ)*(n : ℝ)), one_mul]
    exact hwidth.trans (mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg n))
  have hE (a : ZMod q) : 0 ≤ E a :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hc (a : ℕ) (ha : a ∈ (range (q+1)).filter (fun a => a.Coprime q)) :
      (∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) = E (a : ZMod q) := by
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    have hUnit := (ZMod.isUnit_iff_coprime a q).2 hcop
    let G (β : ℝ) := ‖GoldbachWindow.poly (n+1)
      (GoldbachGRHAnalytic.errorCoeff (a : ZMod q)) β‖^2
    have he (t : ℝ) : G (t - center (q,a)) = ‖primeSum n t - model n (q,a) t‖^2 := by
      unfold G
      rw [GoldbachGRHAnalytic.shifted_error_eq, GoldbachGRHWindow.additiveModel_eq_moebius _ hUnit]
      unfold model
      rw [show (a : ℝ)/q+(t-center (q,a)) = t by unfold center; ring]
    calc
      _ = ∫ t in arcCell n u (q,a), G (t - center (q,a)) := by simp_rw [he]
      _ = E (a : ZMod q) :=
        arcCell_translate hn hu hun hq₂ (Nat.lt_succ_iff.mp (mem_range.mp haq)) hcop G
  have hR : (range (q+1)).filter (fun a => a.Coprime q) =
      (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter,mem_range]
    constructor
    · rintro ⟨ha,hc⟩
      refine ⟨?_,hc⟩
      by_contra! h
      have he : a=q := by omega
      subst a
      simp only [Nat.coprime_self] at hc
      omega
    · rintro ⟨ha,hc⟩
      exact ⟨by omega,hc⟩
  have hcells :
      (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
        ∫ t in arcCell n u (q,a), ‖primeSum n t - model n (q,a) t‖^2) =
        ∑ a : (ZMod q)ˣ, E (a:ZMod q) := by
    rw [sum_congr rfl hc,hR,← inner_sum_units_eq_sum_coprime q
      (fun a : ℕ => E (a:ZMod q))]
    simp only [ZMod.natCast_zmod_val]
  rw [hcells]
  have hden := reducedDenominatorBound (q := q) n h δ hh hd hw
  change (h:ℝ)^2/4*(∑ a : (ZMod q)ˣ,E (a:ZMod q)) ≤ _ at hden
  have he (m:ℕ) : reducedMovingLevelEnergy q n h m =
      ∑ a : (ZMod q)ˣ, ‖GoldbachWindow.moving (n+1) h
        (GoldbachGRHAnalytic.errorCoeff (a:ZMod q)) m‖^2 := by
    simp only [reducedMovingLevelEnergy,dif_neg hq0.ne']
  simp_rw [he]
  linarith only [hden]

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorClippedMoving.lean; sha256 5a8449680d0cf11c927d178b811922b7cf5a99c5f50d4b362d6d55231a2785d9 -/
section
/-! Exact clipped windows and boundary energy. No zero-free assumption. -/
open Finset BombieriVinogradov.LargeSieve InnerFloorLinearTotient
open GoldbachGRHWindow (primeLog additiveModel)
open GoldbachWindow (moving)
open GoldbachGRHAnalytic (errorCoeff)
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def clipStart (h m : ℕ) : ℕ := m+1-h
def clipEnd (n m : ℕ) : ℕ := min m n
def clipLength (n h m : ℕ) : ℕ := clipEnd n m+1-clipStart h m
def clipShift (h m : ℕ) : ℤ := (clipStart h m:ℤ)-1

theorem clipLength_le (n h m : ℕ) : clipLength n h m ≤ h := by
  unfold clipLength clipStart clipEnd
  omega

theorem clipWindow_card (n h m : ℕ) :
    (GBSkirtVariance.window n h m).card = clipLength n h m := by
  rw [GBSkirtVariance.window,Nat.card_Icc]
  unfold clipLength clipStart clipEnd
  omega

theorem clipNatIntSum (n h m : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ℤ → M) :
    (∑ k∈GBSkirtVariance.window n h m, f (k:ℤ)) =
      ∑ k∈Ioc (clipShift h m) (clipShift h m+(clipLength n h m:ℤ)),f k := by
  apply sum_bij (fun (k : ℕ) _ => (k : ℤ))
  · intro k hk
    simp only [GBSkirtVariance.window,mem_Icc] at hk
    simp only [mem_Ioc,clipShift,clipLength,clipStart,clipEnd]
    omega
  · intro a ha b hb he
    exact_mod_cast he
  · intro k hk
    simp only [mem_Ioc,clipShift,clipLength,clipStart,clipEnd] at hk
    have hk0 : 0 ≤ k := by omega
    refine ⟨k.toNat,?_,Int.toNat_of_nonneg hk0⟩
    simp only [GBSkirtVariance.window,mem_Icc]
    omega
  · intro k hk
    rfl

theorem moving_eq_centeredInterval (n h m : ℕ) {q : ℕ} [NeZero q]
    (a : (ZMod q)ˣ) :
    moving (n+1) h (errorCoeff (a:ZMod q)) m =
      intervalAdditiveResidueSum (fun k : ℤ => primeLog k.toNat)
        (clipShift h m) (clipLength n h m) q a -
      (clipLength n h m:ℂ)*additiveModel q (a:ZMod q) := by
  rw [GoldbachWindow.moving_eq_sum]
  have hI : (range (n+1)).filter (fun k => m+1-h ≤ k ∧ k ≤ m) =
      GBSkirtVariance.window n h m := by
    ext k
    simp only [mem_filter,mem_range,GBSkirtVariance.window,mem_Icc,le_min_iff]
    omega
  rw [hI]
  unfold errorCoeff
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,clipWindow_card]
  congr 1
  unfold intervalAdditiveResidueSum
  rw [← clipNatIntSum n h m
    (fun k : ℤ => primeLog k.toNat * ZMod.stdAddChar ((k:ZMod q)*(a:ZMod q)))]
  apply sum_congr rfl
  intro k _
  simp only [Int.toNat_natCast,Int.cast_natCast]
  rw [mul_comm (a:ZMod q) (k:ZMod q)]

theorem reducedMoving_eq_centeredIntervalEnergy (n h m q : ℕ) :
    reducedMovingLevelEnergy q n h m =
      centeredIntervalEnergy (fun k : ℤ => primeLog k.toNat)
        (clipShift h m) (clipLength n h m) q := by
  by_cases hq : q=0
  · simp [reducedMovingLevelEnergy,centeredIntervalEnergy,hq]
  · letI : NeZero q := ⟨hq⟩
    simp only [reducedMovingLevelEnergy,centeredIntervalEnergy,dif_neg hq]
    exact sum_congr rfl fun a _ => by rw [moving_eq_centeredInterval n h m a]

theorem clipShiftedCoefficient_le (n h m k : ℕ)
    (hk : k∈range (clipLength n h m)) :
    ‖shiftedIntervalCoefficients (fun z : ℤ => primeLog z.toNat)
      (clipShift h m) k‖ ≤ Real.log ((n+2:ℕ):ℝ) := by
  let z := (clipShift h m+(k:ℤ)+1).toNat
  have hz : z≤n := by
    have hk' := mem_range.mp hk
    unfold z clipLength clipShift clipStart clipEnd at *
    omega
  change ‖primeLog z‖ ≤ _
  unfold primeLog
  split_ifs with hp
  · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show z≤n+2 by omega))
  · simp only [Complex.ofReal_zero,norm_zero]
    exact Real.log_nonneg (by exact_mod_cast (show 1≤n+2 by omega))

def boundaryWindowBudget (A n h : ℕ) : ℝ :=
  128*((h:ℝ)+(A:ℝ)^2)*(h:ℝ)*(Real.log ((n+2:ℕ):ℝ))^2+
    2*(h:ℝ)^2*(weightConstant*(1+Real.log A))^2

/-- Uniform per-window energy for the actual clipped error coefficients. -/
theorem actualClippedWindowFamilyEnergy (A n h m : ℕ) (hA : 0 < A) :
    (∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m) ≤
      boundaryWindowBudget A n h := by
  simp_rw [reducedMoving_eq_centeredIntervalEnergy]
  apply (centeredIntervalFamilyEnergy A (clipLength n h m) (clipShift h m)
    (fun z : ℤ => primeLog z.toNat) hA (Real.log ((n+2:ℕ):ℝ))
    (Real.log_nonneg (by exact_mod_cast (show 1≤n+2 by omega)))
    (fun k hk => clipShiftedCoefficient_le n h m k hk)).trans
  unfold boundaryWindowBudget
  have hl : (clipLength n h m:ℝ) ≤ h := by exact_mod_cast clipLength_le n h m
  gcongr
  all_goals positivity

theorem reducedMovingLevelEnergy_nonneg (q n h m : ℕ) :
    0 ≤ reducedMovingLevelEnergy q n h m := by
  unfold reducedMovingLevelEnergy
  split_ifs <;> first | exact le_rfl | exact sum_nonneg fun _ _ => sq_nonneg _

/-- Decompose the actual moving family into a bulk primitive window
sum and the at most X+2h endpoint/startup windows. -/
theorem reducedMovingBulkBoundary (A n h X : ℕ)
    (hA : 0 < A) (hAX : A≤X) (hX : X+h≤n) :
    (∑ m∈range (n+1+h), ∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m) ≤
      (weightConstant*(1+Real.log A))^2 *
        (∑ y∈Ico X (n+1-h), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) +
      ((X+2*h:ℕ):ℝ)*boundaryWindowBudget A n h := by
  let S := range (n+1+h)
  let G := Icc (X+h) n
  let E (m : ℕ) := ∑ q∈Icc 1 A,reducedMovingLevelEnergy q n h m
  have hGS : G⊆S := by
    intro m hm
    simp only [G,mem_Icc] at hm
    simp only [S,mem_range]
    omega
  have hcard : (S\G).card = X+2*h := by
    rw [card_sdiff_of_subset hGS]
    simp only [S,G,card_range,Nat.card_Icc]
    omega
  have hbulk :
      (∑ m∈G,E m) ≤ (weightConstant*(1+Real.log A))^2 *
        (∑ y∈Ico X (n+1-h), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) := by
    rw [mul_sum]
    have hre : (∑ m∈G,E m) =
        ∑ y∈Ico X (n+1-h), E (y+h) := by
      apply sum_bij (fun m _ => m-h)
      · intro m hm
        simp only [G,mem_Icc] at hm
        simp only [mem_Ico]
        omega
      · intro m hm k hk he
        simp only [G,mem_Icc] at hm hk
        omega
      · intro y hy
        simp only [mem_Ico] at hy
        refine ⟨y+h,?_,by omega⟩
        simp only [G,mem_Icc]
        omega
      · intro m hm
        simp only [G,mem_Icc] at hm
        rw [Nat.sub_add_cancel (by omega : h ≤ m)]
    rw [hre]
    apply sum_le_sum
    intro y hy
    have hy' := mem_Ico.mp hy
    exact interiorReducedMovingFamilyEnergy A n y h (hAX.trans hy'.1) (by omega)
  have hedge : (∑ m∈S\G,E m) ≤ ((X+2*h:ℕ):ℝ)*boundaryWindowBudget A n h := by
    calc
      _ ≤ ∑ _m∈S\G,boundaryWindowBudget A n h :=
        sum_le_sum fun m _ => actualClippedWindowFamilyEnergy A n h m hA
      _ = _ := by rw [sum_const,nsmul_eq_mul,hcard]
  change (∑ m∈S,E m) ≤ _
  calc
    _ = (∑ m∈G,E m)+(∑ m∈S\G,E m) := by
      rw [add_comm]
      exact (sum_sdiff hGS).symm
    _ ≤ _ := add_le_add hbulk hedge

end
end InnerFloorResearch

end

/-! BEGIN InnerFloorHighBand.lean; sha256 a1f345cd92965679752e323f6d531bc7d7449ea4d24e951ce01770f091c64a21 -/
section
/- Research auxiliary, not the registered theorem. The integral-cover proof adapts
FrontierBand.actualIntegralBound from the accepted BV-band module, preserving its
Apache-2.0 provenance (muxkin, wzhxzkk and OpenAI sources credited in that module).
Changes: arbitrary real width Q and arbitrary subset D; no signed-monotonicity step. -/

open Finset MeasureTheory GoldbachMajorArc GoldbachBDH
open scoped Interval
namespace InnerFloorResearch

def realBandSet (Q : ℝ) (n A B : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, A<q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ Q/((q:ℝ)*n)}

theorem subsetIntegralBound (Q : ℝ) (n A B : ℕ) (D : Set ℝ)
    (hQ : 0 ≤ Q) (hA : 1≤A) (hB : 0<B) (hn : 2≤n)
    (hsub : D ⊆ realBandSet Q n A B) :
    ‖∫ t in (0:ℝ)..1, D.indicator
        (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤
      2*(Q/((A:ℝ)*n))*(((n:ℝ)+1+(B:ℝ)^2)*weightEnergy n) := by
  classical
  let g := fun t => ‖primeSum n t‖^2
  have cg : Continuous g := by dsimp [g,primeSum,phase]; fun_prop
  let R := Q/((A:ℝ)*n)
  have hR : 0≤R := by dsimp [R]; exact div_nonneg hQ (by positivity)
  let center := fun q a : ℕ => (a:ℝ)/q
  let F := fun (q a : ℕ) => (Set.Icc (center q a-R) (center q a+R)).indicator g
  have hF (q a : ℕ) : Integrable (F q a) volume :=
    (cg.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hp (q a : ℕ) (t : ℝ) : 0≤F q a t := by
    by_cases h : t ∈ Set.Icc (center q a-R) (center q a+R)
    · simpa only [F, Set.indicator_of_mem h] using sq_nonneg ‖primeSum n t‖
    · simp [F,h]
  let G := fun t => ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, F q a t
  have hGi : Integrable G volume := integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun a _ => hF q a
  have hGp (t : ℝ) : 0≤G t := sum_nonneg fun q _ => sum_nonneg fun a _ => hp q a t
  have hdom (t : ℝ) : ‖D.indicator (fun t => (primeSum n t)^2*phase (-(n:ℝ)*t)) t‖ ≤ G t := by
    by_cases ht : t∈D
    · rw [Set.indicator_of_mem ht,norm_mul,norm_pow,bandPhase_norm,mul_one]
      obtain ⟨q,a,haq,hqb,ha,hcop,hnear⟩ := hsub ht
      have hq : q∈Finset.Icc 1 B := mem_Icc.mpr ⟨by omega,hqb⟩
      have ha' : a∈num q := by
        refine mem_filter.mpr ⟨mem_range.mpr ?_,hcop⟩
        by_contra! hh
        have heq := Nat.le_antisymm ha hh
        have := (Nat.coprime_self q).mp (heq ▸ hcop)
        omega
      have hrad : Q/((q:ℝ)*n) ≤ R :=
        div_le_div_of_nonneg_left hQ (by positivity) (by gcongr)
      have htF : t∈Set.Icc (center q a-R) (center q a+R) := by
        have h := abs_le.mp (hnear.trans hrad)
        change center q a-R ≤ t ∧ t ≤ center q a+R
        dsimp [center] at *
        constructor <;> linarith [h.1,h.2]
      change g t ≤ _
      calc
        _ = F q a t := (Set.indicator_of_mem htF g).symm
        _ ≤ ∑ b ∈ num q, F q b t := single_le_sum (fun b _ => hp q b t) ha'
        _ ≤ _ := single_le_sum (fun r _ => sum_nonneg fun b _ => hp r b t) hq
    · simpa [ht] using hGp t
  have htranslate (q a : ℕ) :
      (∫ t, F q a t) = ∫ β in -R..R, g (β+center q a) := by
    rw [intervalIntegral.integral_comp_add_right,intervalIntegral.integral_of_le (by linarith)]
    unfold F
    rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
    congr 1 <;> congr 1 <;> ring
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖D.indicator (fun t => (primeSum n t)^2*phase (-(n:ℝ)*t)) t‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t, G t := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hGi.integrableOn (Filter.Eventually.of_forall hdom)).trans
        (setIntegral_le_integral hGi (Filter.Eventually.of_forall hGp))
    _ = ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, ∫ β in -R..R, g (β+center q a) := by
      unfold G
      rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ fun a _ => hF q a)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_finsetSum _ (fun a _ => hF q a)]
      simp_rw [htranslate]
    _ = ∫ β in -R..R, ∑ q ∈ Finset.Icc 1 B, ∑ a ∈ num q, g (β+center q a) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro q _
        rw [intervalIntegral.integral_finsetSum]
        exact fun a _ => (cg.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
      · intro q _
        apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun _ _ => cg.comp (continuous_id.add continuous_const)
    _ ≤ ∫ _β in -R..R, (((n:ℝ)+1+(B:ℝ)^2)*weightEnergy n) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
          cg.comp (continuous_id.add continuous_const)
      · exact continuous_const.intervalIntegrable _ _
      · exact fun t _ => shifted_spectrum n B hB t
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; dsimp [R]; ring


theorem subsetBound (Q : ℝ) (n A B : ℕ) (D : Set ℝ)
    (hQ : 0≤Q) (hA : 1≤A) (hB : 0<B) (hBn : B^2≤n) (hn : 2≤n)
    (hsub : D ⊆ realBandSet Q n A B) :
    ‖∫ t in (0:ℝ)..1, D.indicator
        (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤
      24*(n:ℝ)*Q*(1+Real.log n)^2/A := by
  have h := subsetIntegralBound Q n A B D hQ hA hB hn hsub
  have he := energy_bound n (by omega)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  have hx : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : (0:ℝ)<A := by exact_mod_cast (show 0<A by omega)
  have hc : (n:ℝ)+1+(B:ℝ)^2 ≤ 3*n := by
    have hb : (B:ℝ)^2 ≤ n := by exact_mod_cast hBn
    linarith [show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)]
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have he' : weightEnergy n ≤ 3*n*Real.log n := he.trans (by gcongr)
  have he0 : 0≤weightEnergy n := sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ _ := h
    _ ≤ 2*(Q/((A:ℝ)*n))*((3*n)*(3*n*Real.log n)) := by
      gcongr
    _ = 18*(n:ℝ)*Q*Real.log n/A := by field_simp; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ ha.le
      have he'' : 18*Real.log n ≤ 24*(1+Real.log n)^2 := by nlinarith [sq_nonneg (Real.log (n:ℝ))]
      nlinarith only [mul_le_mul_of_nonneg_left he'' (mul_nonneg hx.le hQ)]

private theorem highBandLog (n : ℕ) (hn : 2≤n) :
    (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
  have hb := Real.natLog_le_logb (n+2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2:ℝ)≤n := by exact_mod_cast hn
  have hh : (n:ℝ)+2 ≤ (n:ℝ)^2 := by nlinarith [mul_nonneg (show 0≤(n:ℝ)-2 by linarith) (show 0≤(n:ℝ)+1 by linarith)]
  have hl := Real.log_le_log (by positivity : 0<(n:ℝ)+2) hh
  rw [Real.log_pow] at hl
  norm_num at hl
  have hx' := (le_div_iff₀ (by linarith : 0<Real.log 2)).mp hb
  have hm := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_)
  linarith only [hl,hx',hm]


open Filter
open scoped Topology

/-- The part with denominators above n^(1/5) has absolute mass o(n), even after
an arbitrary additional mask. The remaining lower-denominator part is not addressed. -/
theorem highBandLittleO (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Set ℝ,
      D ⊆ realBandSet ((Nat.log 2 (n+2):ℝ)^2 * (n:ℝ)^(1/6:ℝ)) n
        ⌊(n:ℝ)^(1/5:ℝ)⌋₊ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ →
      ‖∫ t in (0:ℝ)..1, D.indicator
          (fun t => (primeSum n t)^2 * phase (-(n:ℝ)*t)) t‖ ≤ e*(n:ℝ) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/5)).comp ht
  have hc := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (by norm_num : (0:ℝ)<1/30)).comp_tendsto ht).bound
    (by positivity : 0 < e/4000)
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    hp.eventually_ge_atTop 2,hc] with n hn hL hu hsmall
  intro D hD
  let L := Real.log (n:ℝ)
  let u := (n:ℝ)^(1/5:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  let Q := (Nat.log 2 (n+2):ℝ)^2 * v
  let A : ℕ := ⌊u⌋₊
  let B : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hX : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hu2 : 2≤u := hu
  have hA : 1≤A := Nat.floor_pos.mpr (by linarith : 1≤u)
  have hAp : (0:ℝ)<A := by exact_mod_cast hA
  have hA1 : (1:ℝ)≤A := by exact_mod_cast hA
  have huA : u ≤ 2*(A:ℝ) := by
    have hf := Nat.lt_floor_add_one u
    change u < (A:ℝ)+1 at hf
    linarith
  have hB : 0<B := Nat.floor_pos.mpr (Real.one_le_rpow hX (by norm_num))
  have hBsq : B^2≤n := FrontierBand.denomSquare n hn _ (by norm_num)
  have hv : 0≤v := Real.rpow_nonneg hnR.le _
  have hQ : 0≤Q := mul_nonneg (sq_nonneg _) hv
  have hlog := highBandLog n hn
  have hlogSq := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ)≤_) hlog 2
  have hQb : Q ≤ 16*L^2*v := by
    have h := mul_le_mul_of_nonneg_right hlogSq hv
    dsimp [Q,L] at *
    nlinarith only [h]
  have hL1 : 1≤L := hL
  have hLsq : (1+L)^2 ≤ 4*L^2 := by nlinarith
  have hmul := mul_le_mul hQb hLsq (sq_nonneg _) (by positivity : 0≤16*L^2*v)
  have hs : L^4 ≤ (e/4000)*(n:ℝ)^(1/30:ℝ) := by
    change ‖Real.log (n:ℝ)^(4:ℝ)‖ ≤ (e/4000)*‖(n:ℝ)^(1/30:ℝ)‖ at hsmall
    simpa only [L,Real.rpow_ofNat,Real.norm_of_nonneg (by positivity : 0≤(Real.log (n:ℝ))^4),
      Real.norm_of_nonneg (Real.rpow_nonneg hnR.le (1/30:ℝ))] using hsmall
  have hpow : (n:ℝ)^(1/30:ℝ)*v = u := by
    dsimp [u,v]
    rw [← Real.rpow_add hnR]
    norm_num
  have hbudget : 24*Q*(1+L)^2 ≤ e*(A:ℝ) := by
    calc
      _ ≤ 1536*L^4*v := by nlinarith only [hmul]
      _ ≤ 1536*((e/4000)*(n:ℝ)^(1/30:ℝ))*v := by gcongr
      _ = (1536/4000:ℝ)*e*u := by rw [← hpow]; ring
      _ ≤ e*(A:ℝ) := by
        nlinarith only [mul_le_mul_of_nonneg_left huA he.le,
          mul_nonneg he.le (Nat.cast_nonneg A : (0:ℝ)≤A)]
  have hbound := subsetBound Q n A B D hQ hA hB hBsq hn hD
  refine hbound.trans ?_
  apply (div_le_iff₀ hAp).2
  have h := mul_le_mul_of_nonneg_right hbudget hnR.le
  dsimp [L] at h
  nlinarith only [h]

end InnerFloorResearch

end

/-! BEGIN InnerFloorFrozenAssembly.lean; sha256 23dcd603a10fcbf4bc40776248d12be290fba988edec319953a77538a30fec6a -/
section
open Finset MeasureTheory Filter
open scoped Interval Topology Classical

namespace InnerFloorResearch

noncomputable section
set_option maxHeartbeats 2000000

/-- The exact registered type at origin/main 1fe24b28926c. -/
def FrozenWideRemainderInnerFloor : Prop :=
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
  let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
  let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}
  let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t)
  let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  let H := fun n : ℕ => 256 * Q₁ n * Q n
  let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
  let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
  let lowPart := fun n : ℕ => lowWideArcs n \ arcs n
  let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n
  let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}
  let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re
  let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n)
  floor (fun n => remainder n ∩ inner n)

/-- The only analytic input in this assembly is the actual reduced-cell
model error. It is not the earlier overstrong all-residue variance. -/
def MiddleCellEnergySmall : Prop := ∀ᶠ n : ℕ in atTop,
  mediumCellEnergy n (innerCutoff n) (middleCutoff n) (innerWidth n) ≤
    8*(n:ℝ)/(Real.log (n:ℝ))^4

private theorem mediumIntegral_split {n Q A B : ℕ} {u : ℝ}
    (hn : 0 < n) (hu : 0 ≤ u) (hQA : Q ≤ A) (hAB : A ≤ B)
    (hsep : 2*u*(B : ℝ) < (n : ℝ)) :
    mediumIntegral n Q B u = mediumIntegral n Q A u + mediumIntegral n A B u := by
  let D := mediumBand Q A u (n : ℝ)
  let E := mediumBand A B u (n : ℝ)
  have hd : Disjoint D E := by
    rw [Set.disjoint_left]
    intro t ht ht'
    obtain ⟨q,a,hq,_,hqA,_,hc,ht⟩ := ht
    obtain ⟨r,b,hr,_,hrB,_,hd,ht'⟩ := ht'
    have hh := mediumBand_unique Q B u (n : ℝ) hu (by exact_mod_cast hn)
      hsep hq (hQA.trans_lt hr) (hqA.trans hAB) hrB hc hd ht ht'
    omega
  have hset : mediumBand Q B u (n : ℝ) = D ∪ E := by
    ext t
    constructor
    · rintro ⟨q,a,hq,hq0,hqB,ha,hc,ht⟩
      by_cases hqA : q ≤ A
      · exact Or.inl ⟨q,a,hq,hq0,hqA,ha,hc,ht⟩
      · exact Or.inr ⟨q,a,lt_of_not_ge hqA,hq0,hqB,ha,hc,ht⟩
    · rintro (⟨q,a,hq,hq0,hqA,ha,hc,ht⟩ | ⟨q,a,hq,hq0,hqB,ha,hc,ht⟩)
      · exact ⟨q,a,hq,hq0,hqA.trans hAB,ha,hc,ht⟩
      · exact ⟨q,a,hQA.trans_lt hq,hq0,hqB,ha,hc,ht⟩
  let f := GoldbachGRHApproximation.integrand n
  have hf : Continuous f := by
    unfold f GoldbachGRHApproximation.integrand GoldbachFourthMoment.primeSum GoldbachFourthMoment.phase
    fun_prop
  have hI (s : Set ℝ) (hs : MeasurableSet s) : IntervalIntegrable (s.indicator f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 <|
      (hf.intervalIntegrable 0 1).1.indicator hs
  have hind : (D ∪ E).indicator f = fun t => D.indicator f t + E.indicator f t := by
    ext t
    by_cases hD : t ∈ D
    · have hE : t ∉ E := fun h => Set.disjoint_left.mp hd hD h
      simp [Set.indicator, hD, hE]
    · by_cases hE : t ∈ E <;> simp [Set.indicator, hD, hE]
  unfold mediumIntegral
  rw [hset, hind]
  exact intervalIntegral.integral_add
    (hI D (measurable_mediumBand n Q A u)) (hI E (measurable_mediumBand n A B u))

private theorem signedDifferenceSmall (hEnergy : MiddleCellEnergySmall) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖mediumIntegral n (innerCutoff n) (middleCutoff n) (innerWidth n) -
          mediumModel n (innerCutoff n) (middleCutoff n) (innerWidth n)‖ ≤ ε*(n : ℝ) := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventualInnerGeometry, hEnergy,
    ht.eventually_ge_atTop (max 1 (18/ε))] with n hg hv hL
  obtain ⟨hn, hQ, hQA, hAB, huH, hbudget⟩ := hg
  let L := Real.log (n : ℝ)
  let u := innerWidth n
  let A := middleCutoff n
  let Q := innerCutoff n
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLe : 18/ε ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hu : 0 ≤ u := by unfold u innerWidth; positivity
  have hsep : 2*u*(A : ℝ) < (n : ℝ) := by
    apply lt_of_le_of_lt _ hbudget
    gcongr
  have hun : u ≤ (n : ℝ) := by
    have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hQ.trans hQA
    nlinarith only [hsep, mul_le_mul_of_nonneg_left hA1 hu, hu]
  have hE : mediumCellEnergy n Q A u ≤ 8*(n : ℝ)/L^4 := hv
  have H := signedMediumDifference (Q := Q) hn hu hsep (show 0 < 1/L^3 by positivity)
  change ‖_‖ ≤ (1+1/(1/L^3))*mediumCellEnergy n Q A u + (1/L^3)*((n : ℝ)+1)*L^2 at H
  calc
    _ ≤ _ := H
    _ ≤ (1+1/(1/L^3))*(8*(n : ℝ)/L^4) + (1/L^3)*((n : ℝ)+1)*L^2 := by gcongr
    _ ≤ 18*(n : ℝ)/L := by
      have h3 : 1 ≤ L^3 := one_le_pow₀ hL1
      have hb : (1+1/(1/L^3))*(8*(n : ℝ)/L^4) ≤ 16*(n : ℝ)/L := by
        rw [one_div_one_div]
        calc
          _ ≤ (2*L^3)*(8*(n:ℝ)/L^4) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by field_simp <;> ring
      have hc : (1/L^3)*((n : ℝ)+1)*L^2 ≤ 2*(n : ℝ)/L := by
        rw [show (1/L^3)*((n : ℝ)+1)*L^2 = ((n : ℝ)+1)/L by field_simp <;> ring]
        exact div_le_div_of_nonneg_right (by linarith) hL0.le
      exact (add_le_add hb hc).trans_eq (by ring)
    _ ≤ _ := by
      apply (div_le_iff₀ hL0).2
      have he := (div_le_iff₀ hε).1 hLe
      nlinarith only [mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (n : ℝ))]

/-- The exact frozen type follows if the middle-band cell energy input is
proved. The two signed contributions are combined using the disjoint union. -/
theorem candidate_of_middleCellEnergy (hEnergy : MiddleCellEnergySmall) :
    FrozenWideRemainderInnerFloor := by
  have hFun : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Even n → -(ε*(n : ℝ)) ≤
        (∫ t in (0 : ℝ)..1,
          ((((arcSet (outerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n) \
            (arcSet (innerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n)) ∩
            arcSet (outerCutoff n) (innerWidth n) n).indicator
              (GoldbachGRHApproximation.integrand n)) t).re := by
    intro ε hε
    let e := ε/3
    have he : 0 < e := by unfold e; positivity
    obtain ⟨K, hK⟩ := realWidthModelFloor e he
    filter_upwards [eventualInnerGeometry, GoldbachGRHConcreteFloor.eventually_narrow_ge K,
      signedDifferenceSmall hEnergy e he, highBandLittleO e he]
      with n hg hlarge hdiff hhigh
    intro hnEven
    obtain ⟨hn,hQ,hQA,hAB,huH,hbud⟩ := hg
    let Q := innerCutoff n
    let A := middleCutoff n
    let B := outerCutoff n
    let H := (GoldbachGRHBudget.width n : ℝ)
    let u := innerWidth n
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hu : 0 < u := by
      unfold u innerWidth
      exact mul_pos (by exact_mod_cast hQ) (Real.rpow_pos_of_pos hnR _)
    have huQ : (Q : ℝ) ≤ u := by
      unfold u innerWidth
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hn1 (by norm_num))
    have hQB : Q ≤ B := hQA.trans hAB
    have hB₁ : (1 : ℝ) ≤ B := by exact_mod_cast (hQ.trans hQB)
    have hsep : 2*u*(B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      gcongr
    have hun : 2*u ≤ (n : ℝ) := by
      nlinarith only [hsep, mul_le_mul_of_nonneg_left hB₁ (show 0 ≤ 2*u by positivity)]
    have hmask : u*(Q : ℝ)+H*(B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      have hprod : u*(Q : ℝ) ≤ H*(B : ℝ) :=
        mul_le_mul huH (by exact_mod_cast hQB) (Nat.cast_nonneg _) (hu.le.trans huH)
      linarith only [hprod]
    rw [inner_remainder_eq Q B (Q : ℝ) H u (n : ℝ) (huQ.trans huH) huH hnR.le,
      masked_medium_eq Q B u H (n : ℝ) hu.le huH hnR hmask]
    change -(ε*(n : ℝ)) ≤ (mediumIntegral n Q B u).re
    rw [mediumIntegral_split (by omega) hu.le hQA hAB hsep, Complex.add_re]
    have hM := hK n Q A (by omega) hnEven hQ hlarge hQA u hu hun
    have hD : |(mediumIntegral n Q A u - mediumModel n Q A u).re| ≤ e*(n : ℝ) :=
      (Complex.abs_re_le_norm _).trans hdiff
    have hHigh' : ‖mediumIntegral n A B u‖ ≤ e*(n : ℝ) := by
      have hu' : u = (Nat.log 2 (n+2) : ℝ)^2 * (n : ℝ)^(1/6 : ℝ) := by
        unfold u innerWidth innerCutoff GoldbachGRHBudget.narrow
        push_cast <;> rfl
      have H := hhigh (mediumBand A B u n) (by
        intro t ht
        obtain ⟨q,a,hq,_,hqB,ha,hcop,ht⟩ := ht
        exact ⟨q,a,hq,hqB,ha,hcop,hu' ▸ ht⟩)
      exact H
    have hHigh := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hHigh')
    have hD' := neg_le_of_abs_le hD
    rw [Complex.sub_re] at hD'
    unfold e at hM hD' hHigh
    linarith only [hM, hD', hHigh]
  intro ε hε
  exact Filter.eventually_atTop.mp (hFun ε hε)

/-- One-sided signed middle-band floor: strictly weaker than the L2 energy
    hypothesis `MiddleCellEnergySmall`, preserving all sign cancellation
    between the prime sum and the principal model. -/
def SignedMiddleRemainderFloor : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, Even n →
    -(ε * (n : ℝ)) ≤
      (mediumIntegral n (innerCutoff n) (middleCutoff n) (innerWidth n) -
        mediumModel n (innerCutoff n) (middleCutoff n) (innerWidth n)).re

/-- Unconditional reduction of the exact frozen statement
    `FrozenWideRemainderInnerFloor` to the one-sided signed middle-band floor
    (without requiring the two-sided L2 bound `MiddleCellEnergySmall`). -/
theorem candidate_of_signedMiddleFloor (hSigned : SignedMiddleRemainderFloor) :
    FrozenWideRemainderInnerFloor := by
  have hFun : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Even n → -(ε * (n : ℝ)) ≤
        (∫ t in (0 : ℝ)..1,
          ((((arcSet (outerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n) \
            (arcSet (innerCutoff n) (GoldbachGRHBudget.width n : ℝ) n \
              arcSet (innerCutoff n) (innerCutoff n : ℝ) n)) ∩
            arcSet (outerCutoff n) (innerWidth n) n).indicator
              (GoldbachGRHApproximation.integrand n)) t).re := by
    intro ε hε
    let e := ε / 3
    have he : 0 < e := by unfold e; positivity
    obtain ⟨K, hK⟩ := realWidthModelFloor e he
    filter_upwards [eventualInnerGeometry, GoldbachGRHConcreteFloor.eventually_narrow_ge K,
      hSigned e he, highBandLittleO e he]
      with n hg hlarge hdiff hhigh
    intro hnEven
    obtain ⟨hn, hQ, hQA, hAB, huH, hbud⟩ := hg
    let Q := innerCutoff n
    let A := middleCutoff n
    let B := outerCutoff n
    let H := (GoldbachGRHBudget.width n : ℝ)
    let u := innerWidth n
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hu : 0 < u := by
      unfold u innerWidth
      exact mul_pos (by exact_mod_cast hQ) (Real.rpow_pos_of_pos hnR _)
    have huQ : (Q : ℝ) ≤ u := by
      unfold u innerWidth
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hn1 (by norm_num))
    have hQB : Q ≤ B := hQA.trans hAB
    have hB₁ : (1 : ℝ) ≤ B := by exact_mod_cast (hQ.trans hQB)
    have hsep : 2 * u * (B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      gcongr
    have hun : 2 * u ≤ (n : ℝ) := by
      nlinarith only [hsep, mul_le_mul_of_nonneg_left hB₁ (show 0 ≤ 2 * u by positivity)]
    have hmask : u * (Q : ℝ) + H * (B : ℝ) < (n : ℝ) := by
      apply lt_of_le_of_lt _ hbud
      have hprod : u * (Q : ℝ) ≤ H * (B : ℝ) :=
        mul_le_mul huH (by exact_mod_cast hQB) (Nat.cast_nonneg _) (hu.le.trans huH)
      linarith only [hprod]
    rw [inner_remainder_eq Q B (Q : ℝ) H u (n : ℝ) (huQ.trans huH) huH hnR.le,
      masked_medium_eq Q B u H (n : ℝ) hu.le huH hnR hmask]
    change -(ε * (n : ℝ)) ≤ (mediumIntegral n Q B u).re
    rw [mediumIntegral_split (by omega) hu.le hQA hAB hsep, Complex.add_re]
    have hM := hK n Q A (by omega) hnEven hQ hlarge hQA u hu hun
    have hD' := hdiff hnEven
    rw [Complex.sub_re] at hD'
    have hHigh' : ‖mediumIntegral n A B u‖ ≤ e * (n : ℝ) := by
      have hu' : u = (Nat.log 2 (n + 2) : ℝ) ^ 2 * (n : ℝ) ^ (1 / 6 : ℝ) := by
        unfold u innerWidth innerCutoff GoldbachGRHBudget.narrow
        push_cast <;> rfl
      have H := hhigh (mediumBand A B u n) (by
        intro t ht
        obtain ⟨q, a, hq, _, hqB, ha, hcop, ht⟩ := ht
        exact ⟨q, a, hq, hqB, ha, hcop, hu' ▸ ht⟩)
      exact H
    have hHigh := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hHigh')
    unfold e at hM hD' hHigh
    linarith only [hM, hD', hHigh]
  intro ε hε
  exact Filter.eventually_atTop.mp (hFun ε hε)

#print axioms candidate_of_signedMiddleFloor

end
end InnerFloorResearch
end

end PartI_SignedFrozenReduction

section PartII_RouteBResearch
section

/-!
# Wide Remainder Inner Floor — Unified Route B + Independent Odd-Residual Pre-PR File

Target task: `L-goldbach-wide-remainder-inner-floor`
Target file: `lean/Conjectures/Goldbach/WideRemainderInnerFloor.lean`

Unifies ALL independently Colab-verified Route B & independent-odd-residual modules
under pinned Lean 4.36.0 / Mathlib `fc4f59e`, standard foundational axioms only
(`propext`, `Classical.choice`, `Quot.sound`), zero `sorry`, zero GRH imports:
1. `InnerFloorOccurrence`: 3,218-line end-to-end tapered zero-occurrence residual floor.
2. `InnerFloorRouteB`: signed bilinear cell floor, model–bad cross vanishing at `q ∣ n`,
   primitive quadratic Gauss square, and 3-way parity/reality partition.
3. `InnerFloorRouteBThreshold`: even real diagonal nonnegativity and exact necessity /
   sufficiency log-gap thresholds.
4. `InnerFloorRouteBAlmostAll`: unconditional Gate-3 high-gcd exceptional-set density bound.
5. `InnerFloorRouteBFourGate`: 4-gate quantitative residual partition (adding imaginary height
   `|γ|` gate), exact joint Gauss–Ramanujan negative countermodel (`d = 3p`, `n = 2p^8`),
   and global mod-`3p` parity annihilation proof (`global_mod3_forced_one`, `global_modp_neg`).
6. `InnerFloorIndependentEulerMass` / `InnerFloorIndependentCross` /
   `InnerFloorIndependentRealKernel` / `InnerFloorIndependentRelativeSign`:
   odd squarefree totient tail, localized real-zero cross saving, finite-frequency
   real-kernel L2 perturbation `∫₀¹ (x^(β-1)-1)² dx ≤ (16/3)(1-β)²`, and weighted relative floor.
7. `Conjectures.Goldbach`: exact frozen statement with the single isolated open-problem
   barrier (`JointNegativeNearOneZeroBarrier`) explicitly declared at the top level.
-/



/-!
Small independently replayable arithmetic interface extracted from
ShortProgressionsMeanTheta (XBribo, PR #3789,
a546c6629fae0223b56067d5e4ebc34043c4fbf1, Apache-2.0).
Names relocated to avoid duplicate OAI.Ostmann declarations when used
with DyadicCellShortPrimeFloor. Only elementary definitions and lemmas
are copied; none of the analytic black-box conclusions are assumed.
-/
open Finset Filter
open scoped Topology Classical
noncomputable section
namespace RouteB_InnerFloorLinearTotient
set_option maxHeartbeats 1000000 in


private def squareMass : ℝ := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
set_option maxHeartbeats 1000000 in

private theorem squareMass_nonneg : 0 ≤ squareMass := tsum_nonneg fun _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem sum_square_inv_le (s : Finset ℕ) :
    (∑ n ∈ s, ((n:ℝ)^2)⁻¹) ≤ squareMass :=
  (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2:ℕ))).sum_le_tsum s fun _ _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem one_le_squareMass : 1 ≤ squareMass := by
  simpa using sum_square_inv_le {(1:ℕ)}

set_option maxHeartbeats 1000000 in
/-- Uniform constant for the reciprocal-totient mean and conductor lifting. -/
def weightConstant : ℝ := Real.exp (2*squareMass) * squareMass
set_option maxHeartbeats 1000000 in

theorem weightConstant_nonneg : 0 ≤ weightConstant :=
  mul_nonneg (Real.exp_pos _).le squareMass_nonneg
set_option maxHeartbeats 1000000 in

private theorem prime_factor_bound {p : ℕ} (hp : 2 ≤ p) :
    (1-(p:ℝ)⁻¹)⁻¹ ≤ (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) := by
  let u := (p:ℝ)⁻¹
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu' : u ≤ 1/2 := by
    change (p:ℝ)⁻¹ ≤ 1/2
    rw [← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hp'
  have hden : 0 < 1-u := by linarith
  have hsq : u^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hu hu' 2
  have hnon := mul_nonneg (sq_nonneg u) (show 0 ≤ 1-2*u^2 by linarith)
  rw [← inv_pow]
  change (1-u)⁻¹ ≤ (1+u)*(1+2*u^2)
  rw [← one_div, div_le_iff₀ hden]
  nlinarith only [hnon]
set_option maxHeartbeats 1000000 in

private theorem squarefree_product_eq (q : ℕ) (hq : 0 < q) :
    (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) = ∑ d ∈ q.divisors with Squarefree d, (d:ℝ)⁻¹ := by
  rw [Finset.prod_one_add, Nat.sum_divisors_filter_squarefree hq.ne', Nat.factors_eq]
  refine sum_congr rfl fun s _ => ?_
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
  rw [Finset.prod_eq_multiset_prod, show (fun i : ℕ => i) = id from rfl, Multiset.map_id]
set_option maxHeartbeats 1000000 in

private theorem ratio_le_divisors (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hEuler : (q.totient:ℝ) = (q:ℝ)*∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹) := by
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀] using
      congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors q)
  have hlocal (p : ℕ) (hp : p ∈ q.primeFactors) : 0 ≤ (1-(p:ℝ)⁻¹)⁻¹ := by
    have hp' : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    apply inv_nonneg.mpr
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by linarith)
  have hsq : (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) ≤ Real.exp (2*squareMass) := by
    apply (Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)).trans
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_square_inv_le _) (by norm_num)
  calc
    _ = ∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹)⁻¹ := by
      rw [hEuler, div_mul_eq_div_div, div_self hq'.ne', one_div, Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) :=
      prod_le_prod₀ hlocal fun p hp => prime_factor_bound (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) :=
      Finset.prod_mul_distrib
    _ ≤ (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * Real.exp (2*squareMass) :=
      mul_le_mul_of_nonneg_left hsq (prod_nonneg fun _ _ => by positivity)
    _ ≤ _ := by
      rw [mul_comm, squarefree_product_eq q hq]
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)) (Real.exp_pos _).le
set_option maxHeartbeats 1000000 in

private theorem harmonic_bound (Q : ℕ) :
    (∑ i ∈ Icc 1 Q, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log Q

set_option maxHeartbeats 1000000 in
/-- Pointwise `q/φ(q)` also costs at most one logarithm. -/
theorem ratio_totient_le (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ weightConstant * (1+Real.log q) := by
  have hsub : q.divisors ⊆ Icc 1 q := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)⟩
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q from hq))
  calc
    _ ≤ Real.exp (2*squareMass) * (1+Real.log q) :=
      (ratio_le_divisors q hq).trans (mul_le_mul_of_nonneg_left
        ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (harmonic_bound q))
        (Real.exp_pos _).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (Real.exp_pos _).le one_le_squareMass) (by positivity)
set_option maxHeartbeats 1000000 in

private theorem sum_antidiagonal_le_product (Q : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal, f ab.1*g ab.2) ≤
      (∑ a ∈ Icc 1 Q, f a)*(∑ b ∈ Icc 1 Q, g b) := by
  let S := Icc 1 Q
  let w (p : ℕ × ℕ) := f p.1*g p.2
  have hw (p : ℕ × ℕ) : 0 ≤ w p := mul_nonneg (hf _) (hg _)
  have hsub (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal ⊆ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    intro ab hab
    have hm (d : ℕ) (hd : d ∈ q.divisors) : d ∈ S :=
      mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd (mem_Icc.mp hq).1 (Nat.dvd_of_mem_divisors hd)).trans (mem_Icc.mp hq).2⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
      hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
  change (∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab) ≤ _
  calc
    _ ≤ ∑ q ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w p :=
      sum_le_sum fun q hq => sum_le_sum_of_subset_of_nonneg (hsub q hq) (fun p _ _ => hw p)
    _ = ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w p :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ S ×ˢ S, w p := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hw p)
    _ = (∑ a ∈ S, f a)*(∑ b ∈ S, g b) := by rw [sum_product, sum_mul_sum]
set_option maxHeartbeats 1000000 in

private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1/(q.totient:ℝ) ≤ Real.exp (2*squareMass) *
      ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  calc
    _ = ((q:ℝ)/(q.totient:ℝ))/q := by
      rw [div_right_comm, div_self hq'.ne']
    _ ≤ (Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹)/q :=
      div_le_div_of_nonneg_right (ratio_le_divisors q hq) hq'.le
    _ = _ := by
      rw [mul_div_assoc, Finset.sum_div,
        ← Nat.sum_divisorsAntidiagonal (fun d _ => (d:ℝ)⁻¹/q) (n := q)]
      congr 1
      refine sum_congr rfl fun p hp => ?_
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul, div_eq_mul_inv,
        mul_inv, ← inv_pow, pow_two, mul_assoc]

set_option maxHeartbeats 1000000 in
/-- The sum of reciprocal totients costs one logarithm, uniformly in `Q`. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1/(q.totient:ℝ)) ≤ weightConstant * (1+Real.log Q) := by
  calc
    _ ≤ Real.exp (2*squareMass) * (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal,
        ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1
    _ ≤ Real.exp (2*squareMass) * ((∑ a ∈ Icc 1 Q, ((a:ℝ)^2)⁻¹)*(∑ b ∈ Icc 1 Q, (b:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (sum_antidiagonal_le_product Q (fun a => ((a:ℝ)^2)⁻¹) (fun b => (b:ℝ)⁻¹)
        (fun _ => by positivity) (fun _ => by positivity)) (Real.exp_pos _).le
    _ ≤ Real.exp (2*squareMass) * (squareMass*(1+Real.log Q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (sum_square_inv_le _) (harmonic_bound Q)
        (sum_nonneg fun _ _ => by positivity) squareMass_nonneg) (Real.exp_pos _).le
    _ = _ := (mul_assoc ..).symm

set_option maxHeartbeats 1000000 in
/-- Conductor multiplicities lose a single logarithm, including `d = 1`. -/
theorem sum_conductor_weights (Q : ℕ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ q ∈ Icc 1 Q, (∑ d ∈ q.divisors, F d)/(q.totient:ℝ)) ≤
      (∑ d ∈ Icc 1 Q, F d/(d.totient:ℝ)) * (weightConstant*(1+Real.log Q)) := by
  let f (d : ℕ) := F d/(d.totient:ℝ)
  let g (m : ℕ) := 1/(m.totient:ℝ)
  have hf (d : ℕ) : 0 ≤ f d := div_nonneg (hF d) (Nat.cast_nonneg _)
  have hg (m : ℕ) : 0 ≤ g m := by dsimp [g]; positivity
  have hterm (q : ℕ) : (∑ d ∈ q.divisors, F d)/(q.totient:ℝ) ≤
      ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := by
    rw [Finset.sum_div, ← Nat.sum_divisorsAntidiagonal (fun d _ => F d/(q.totient:ℝ)) (n := q)]
    refine sum_le_sum fun p hp => ?_
    have h1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have h2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    have h3 : 0 < (p.1.totient:ℝ)*(p.2.totient:ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.totient_pos.mpr h1) (Nat.totient_pos.mpr h2)
    have hφ := Nat.totient_super_multiplicative p.1 p.2
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1] at hφ
    calc
      _ ≤ F p.1/((p.1.totient:ℝ)*(p.2.totient:ℝ)) :=
        div_le_div_of_nonneg_left (hF _) h3 (by exact_mod_cast hφ)
      _ = _ := by
        simp only [f, g, div_eq_mul_inv, one_mul, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := sum_le_sum fun q _ => hterm q
    _ ≤ (∑ d ∈ Icc 1 Q, f d)*(∑ m ∈ Icc 1 Q, g m) := sum_antidiagonal_le_product Q f g hf hg
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_totient_le Q) (sum_nonneg fun d _ => hf d)


/-- Uniform finite sum of reciprocal m*phi(m), with no logarithmic loss.
The antidiagonal inequality uses the divisor expansion already proved above. -/
theorem sum_inv_mul_totient_le (M : ℕ) :
    (∑ m ∈ Icc 1 M, (1:ℝ)/((m:ℝ)*(m.totient:ℝ))) ≤
      weightConstant * squareMass := by
  calc
    _ ≤ Real.exp (2*squareMass) *
        (∑ m ∈ Icc 1 M, ∑ ab ∈ m.divisorsAntidiagonal,
          ((ab.1:ℝ)^2)⁻¹ * ((ab.2:ℝ)^2)⁻¹) := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro m hm
      have hm0 : 0 < (m:ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
      calc
        _ = (1/(m.totient:ℝ))/(m:ℝ) := by ring
        _ ≤ (Real.exp (2*squareMass) *
              ∑ ab ∈ m.divisorsAntidiagonal,
                ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹)/(m:ℝ) :=
          div_le_div_of_nonneg_right (inv_totient_le_pairs m (mem_Icc.mp hm).1) hm0.le
        _ = Real.exp (2*squareMass) *
              ∑ ab ∈ m.divisorsAntidiagonal,
                (((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹)/(m:ℝ) := by
          rw [mul_div_assoc, Finset.sum_div]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply sum_le_sum
          intro p hp
          have ha : 1 ≤ p.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
          have hb : 1 ≤ p.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
          have haR : (1:ℝ) ≤ p.1 := by exact_mod_cast ha
          have hbR : (1:ℝ) ≤ p.2 := by exact_mod_cast hb
          have ha0 : (0:ℝ) < p.1 := by linarith
          have hb0 : (0:ℝ) < p.2 := by linarith
          rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul]
          apply (div_le_iff₀ (mul_pos ha0 hb0)).2
          have h := mul_le_mul_of_nonneg_right haR (show 0 ≤ ((p.1:ℝ)^2)⁻¹ * (p.2:ℝ)⁻¹ by positivity)
          calc
            _ ≤ (p.1:ℝ) * (((p.1:ℝ)^2)⁻¹ * (p.2:ℝ)⁻¹) := by simpa using h
            _ = ((p.1:ℝ)^2)⁻¹ * ((p.2:ℝ)^2)⁻¹ * ((p.1:ℝ)*(p.2:ℝ)) := by
              field_simp <;> ring
    _ ≤ Real.exp (2*squareMass) *
        ((∑ a ∈ Icc 1 M, ((a:ℝ)^2)⁻¹) *
          (∑ b ∈ Icc 1 M, ((b:ℝ)^2)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (sum_antidiagonal_le_product M (fun a => ((a:ℝ)^2)⁻¹)
          (fun b => ((b:ℝ)^2)⁻¹) (fun _ => by positivity) (fun _ => by positivity))
        (Real.exp_pos _).le
    _ ≤ Real.exp (2*squareMass) * (squareMass * squareMass) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (sum_square_inv_le _) (sum_square_inv_le _)
          (sum_nonneg fun _ _ => by positivity) squareMass_nonneg) (Real.exp_pos _).le
    _ = _ := by unfold weightConstant; ring

/-- Explicit uniform constant, independent of the conductor and the cutoff. -/
def exceptionalWeightConstant : ℝ := weightConstant * squareMass

theorem exceptionalWeightConstant_nonneg : 0 ≤ exceptionalWeightConstant :=
  mul_nonneg weightConstant_nonneg squareMass_nonneg

/-- Finite weighted bound for the isolated zero-model diagonal.
The hypotheses expose the two analytic/arithmetic inputs separately:
the coefficient is bounded by 1/phi(m), and the integral by C*U/(d*m).
No assertion about actual prime sums is made. -/
theorem isolatedPacket_bound (S : Finset ℕ) (M d : ℕ) (hd : 0 < d)
    (hS : S ⊆ Icc 1 M) (U C X : ℝ) (hU : 0 ≤ U)
    (hC : 0 ≤ C) (hX : 0 ≤ X) (a I : ℕ → ℝ)
    (ha : ∀ m ∈ S, |a m| ≤ 1/(m.totient:ℝ))
    (hI : ∀ m ∈ S, |I m| ≤ C*U/((d:ℝ)*(m:ℝ))) :
    |((d:ℝ)/(d.totient:ℝ))*X*(∑ m ∈ S, a m * I m)| ≤
      C*exceptionalWeightConstant*X*U/(d.totient:ℝ) := by
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hphi : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hnon : 0 ≤ (d:ℝ)/(d.totient:ℝ)*X := by positivity
  have hsum : (∑ m ∈ S, 1/((m:ℝ)*(m.totient:ℝ))) ≤ exceptionalWeightConstant :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (sum_inv_mul_totient_le M)
  rw [abs_mul, abs_of_nonneg hnon]
  calc
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*(∑ m ∈ S, |a m * I m|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hnon
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*
        (∑ m ∈ S, (C*U/(d:ℝ))*(1/((m:ℝ)*(m.totient:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hnon
      apply sum_le_sum
      intro m hm
      rw [abs_mul]
      calc
        _ ≤ (1/(m.totient:ℝ))*(C*U/((d:ℝ)*(m:ℝ))) :=
          mul_le_mul (ha m hm) (hI m hm) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*(C*U/(d:ℝ)*exceptionalWeightConstant) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hnon
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp <;> ring

/-- The common-conductor packet estimate. For two primitive characters
of conductors d1 and d2, take L = lcm d1 d2 and g = sqrt(d1*d2).
The Gauss bound and the common-level totient inequality yield the
hypothesis on a. No sign or independence assumption is made. -/
theorem commonMultiplePacket_bound (S : Finset ℕ) (M L : ℕ) (hL : 0 < L)
    (hS : S ⊆ Icc 1 M) (g U C X : ℝ) (hg : 0 ≤ g) (hgL : g ≤ L)
    (hU : 0 ≤ U) (hC : 0 ≤ C) (hX : 0 ≤ X) (a I : ℕ → ℝ)
    (ha : ∀ m ∈ S, |a m| ≤ g/((L*m).totient:ℝ))
    (hI : ∀ m ∈ S, |I m| ≤ C*U/((L*m:ℕ):ℝ)) :
    |X*(∑ m ∈ S, a m * I m)| ≤
      C*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  have hLR : 0 < (L:ℝ) := by exact_mod_cast hL
  have hphi : 0 < (L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hL
  have hsum : (∑ m ∈ S, 1/((m:ℝ)*(m.totient:ℝ))) ≤ exceptionalWeightConstant :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (sum_inv_mul_totient_le M)
  have hterm (m : ℕ) (hm : m ∈ S) :
      |a m*I m| ≤ (C*U/(L.totient:ℝ))*(1/((m:ℝ)*(m.totient:ℝ))) := by
    have hm0 : 0 < m := (mem_Icc.mp (hS hm)).1
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm0
    have hmφ : 0 < (m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm0
    have hφ : (L.totient:ℝ)*(m.totient:ℝ) ≤ ((L*m).totient:ℝ) := by
      exact_mod_cast Nat.totient_super_multiplicative L m
    have hal := (ha m hm).trans (div_le_div_of_nonneg_left hg (mul_pos hphi hmφ) hφ)
    rw [abs_mul]
    calc
      _ ≤ (g/((L.totient:ℝ)*(m.totient:ℝ)))*(C*U/((L*m:ℕ):ℝ)) :=
        mul_le_mul hal (hI m hm) (abs_nonneg _) (by positivity)
      _ ≤ ((L:ℝ)/((L.totient:ℝ)*(m.totient:ℝ)))*(C*U/((L*m:ℕ):ℝ)) := by
        gcongr
      _ = _ := by rw [Nat.cast_mul]; field_simp <;> ring
  rw [abs_mul,abs_of_nonneg hX]
  calc
    _ ≤ X*(∑ m ∈ S, |a m*I m|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hX
    _ ≤ X*(∑ m ∈ S, (C*U/(L.totient:ℝ))*(1/((m:ℝ)*(m.totient:ℝ)))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) hX
    _ ≤ X*(C*U/(L.totient:ℝ)*exceptionalWeightConstant) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (by positivity)) hX
    _ = _ := by ring

/-- The conductor weight is uniformly little-o after any fixed polylog loss.
This handles arbitrary finite pairs whose lcm is at least n^(1/6+delta). -/
theorem eventualLargeConductorWeight (δ k ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (n:ℝ)^(1/6+δ) ≤ d → d ≤ n →
      (Real.log (n:ℝ))^k*(n:ℝ)^(1/6:ℝ)/(d.totient:ℝ) ≤ ε := by
  have hnlim : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  let W := weightConstant
  have hW : 0 ≤ W := weightConstant_nonneg
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (k+1) hδ).comp_tendsto hnlim).bound
    (show 0 < ε/(2*W+1) by positivity)
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp hnlim).eventually_ge_atTop 1,hsmall]
    with n hn hlog hsmall
  intro d hd hdn
  let L := Real.log (n:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  let w := (n:ℝ)^δ
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL1 : 1 ≤ L := hlog
  have hL0 : 0 < L := by linarith
  have hv : 0 < v := Real.rpow_pos_of_pos hn0 _
  have hw : 0 < w := Real.rpow_pos_of_pos hn0 _
  have hpow : v*w = (n:ℝ)^(1/6+δ) := by
    dsimp [v,w]
    rw [← Real.rpow_add hn0]
  have hvd : v*w ≤ (d:ℝ) := by rw [hpow]; exact hd
  have hdR : 0 < (d:ℝ) := (mul_pos hv hw).trans_le hvd
  have hdN : 0 < d := by exact_mod_cast hdR
  have hφ : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hdN
  have hdnR : (d:ℝ) ≤ n := by exact_mod_cast hdn
  have hlogd : Real.log (d:ℝ) ≤ L := Real.log_le_log hdR hdnR
  have hratio : (d:ℝ)/(d.totient:ℝ) ≤ 2*W*L := by
    calc
      _ ≤ W*(1+Real.log d) := ratio_totient_le d hdN
      _ ≤ W*(2*L) := mul_le_mul_of_nonneg_left (by linarith) hW
      _ = _ := by ring
  have hvw : v/(d:ℝ) ≤ 1/w := by
    rw [div_le_div_iff₀ hdR hw]
    simpa using hvd
  have hsl : L^(k+1) ≤ ε/(2*W+1)*w := by
    change ‖Real.log (n:ℝ)^(k+1)‖ ≤ ε/(2*W+1)*‖(n:ℝ)^δ‖ at hsmall
    simpa only [L,w,Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hsmall
  have hpowL : L^k*L = L^(k+1) := by
    rw [Real.rpow_add hL0,Real.rpow_one]
  change L^k*v/(d.totient:ℝ) ≤ ε
  calc
    _ = L^k*((d:ℝ)/(d.totient:ℝ))*(v/(d:ℝ)) := by field_simp <;> ring
    _ ≤ L^k*(2*W*L)*(1/w) := by gcongr
    _ = 2*W*(L^(k+1)/w) := by rw [← hpowL]; ring
    _ ≤ 2*W*(ε/(2*W+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_iff₀ hw).2 hsl
    _ ≤ ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2*W+1)).2
      linarith

end RouteB_InnerFloorLinearTotient

end



/-! Uniform, sign-independent estimates for the exact continuous zero
models on the scaled inner arcs. No zero-free hypothesis or assertion
about actual primes is used in these lemmas. -/
open MeasureTheory
open scoped Interval
namespace InnerFloorZeroModel
noncomputable section

def phase (s : ℝ) : ℂ := Complex.exp ((s:ℂ)*Complex.I)

@[simp] theorem norm_phase (s : ℝ) : ‖phase s‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I s

def transform (β γ v : ℝ) : ℂ :=
  ∫ x in (0:ℝ)..1, (x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)

theorem transform_norm_le (β γ v : ℝ) (hβ : 0 < β) :
    ‖transform β γ v‖ ≤ 1/β := by
  unfold transform
  apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans_eq
  have he : (∫ x in (0:ℝ)..1,
        ‖(x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)‖) =
      ∫ x in (0:ℝ)..1, x^(β-1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    change ‖(x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)‖ = x^(β-1)
    rw [norm_smul, norm_phase, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx.1 _)]
  rw [he, integral_rpow (Or.inl (by linarith : -1 < β-1))]
  rw [show β-1+1=β by ring, Real.one_rpow, Real.zero_rpow hβ.ne', sub_zero]

def pairIntegral (β₁ γ₁ β₂ γ₂ L : ℝ) : ℂ :=
  ∫ v in (-L)..L, transform β₁ γ₁ v * transform β₂ γ₂ v *
    phase (-(2*Real.pi*v))

theorem pairIntegral_norm_le (β₁ γ₁ β₂ γ₂ L : ℝ)
    (h₁ : 0 < β₁) (h₂ : 0 < β₂) (hL : 0≤L) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ L‖ ≤ (2*L)/(β₁*β₂) := by
  unfold pairIntegral
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -L) (b := L) (C := (1/β₁)*(1/β₂))
    (f := fun v => transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v)))
    (fun v _ => by
      rw [norm_mul, norm_mul, norm_phase, mul_one]
      exact mul_le_mul (transform_norm_le β₁ γ₁ v h₁)
        (transform_norm_le β₂ γ₂ v h₂) (norm_nonneg _) (by positivity))
  calc
    _ ≤ |L-(-L)| * ((1/β₁)*(1/β₂)) := by simpa [mul_comm] using h
    _ = _ := by rw [abs_of_nonneg (by linarith)]; ring

/-- Uniform bound for near-one pairs (valid throughout beta >= 1/2). -/
theorem pairIntegral_nearOne (β₁ γ₁ β₂ γ₂ L : ℝ)
    (h₁ : 1/2≤β₁) (h₂ : 1/2≤β₂) (hL : 0≤L) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ L‖ ≤ 8*L := by
  apply (pairIntegral_norm_le β₁ γ₁ β₂ γ₂ L (by linarith) (by linarith) hL).trans
  have hb : 1/4 ≤ β₁*β₂ := by
    have := mul_le_mul h₁ h₂ (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤β₁)
    linarith
  calc
    _ ≤ (2*L)/(1/4:ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hb
    _ = _ := by ring

end
end InnerFloorZeroModel

open Finset Filter RouteB_InnerFloorLinearTotient
open scoped Classical Topology
namespace InnerFloorZeroModel
noncomputable section
set_option maxHeartbeats 2000000

/-- Actual continuous pair-integrals fit the verified conductor-packet
bound for all gamma, not just for real zeros. The arithmetic coefficient
bound must still be supplied by the actual Gauss-character expansion. -/
theorem continuousPacket_bound (S : Finset ℕ) (M L : ℕ) (hL : 0 < L)
    (hS : S ⊆ Icc 1 M) (g U X β₁ γ₁ β₂ γ₂ : ℝ)
    (hg : 0≤g) (hgL : g≤L) (hU : 0≤U) (hX : 0≤X)
    (hβ₁ : 1/2≤β₁) (hβ₂ : 1/2≤β₂)
    (a : ℕ → ℂ)
    (ha : ∀ m∈S, ‖a m‖≤g/((L*m).totient:ℝ)) :
    ‖(X:ℂ)*(∑ m∈S, a m * pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ)))‖ ≤
      8*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  let I (m : ℕ) := pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ))
  have hI : ∀ m∈S, |‖I m‖|≤8*U/((L*m:ℕ):ℝ) := by
    intro m hm
    rw [abs_of_nonneg (norm_nonneg _)]
    have h := pairIntegral_nearOne β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ))
      hβ₁ hβ₂ (by positivity)
    dsimp [I]
    exact h.trans_eq (by ring)
  have hW := commonMultiplePacket_bound S M L hL hS g U 8 X hg hgL hU
    (by norm_num) hX (fun m => ‖a m‖) (fun m => ‖I m‖)
    (fun m hm => by simpa only [abs_of_nonneg (norm_nonneg _)] using ha m hm) hI
  have hsum0 : 0≤X*(∑ m∈S, ‖a m‖*‖I m‖) :=
    mul_nonneg hX (sum_nonneg fun m _ => by positivity)
  rw [abs_of_nonneg hsum0] at hW
  change ‖(X:ℂ)*(∑ m∈S, a m*I m)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX]
  apply le_trans _ hW
  apply mul_le_mul_of_nonneg_left _ hX
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])

/-- A finite family of large-common-conductor model pairs with any fixed
polylogarithmic cardinality and beta <= 1 is negligible in total.
The input U <= C * log(n)^2 * n^(1/6) is the frozen inner width. -/
theorem sparseLargePackets_o (δ k C ε : ℝ) (hδ : 0 < δ) (hC : 0≤C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (T : Finset ℕ) (D : ℕ → ℕ) (J : ℕ → ℂ),
        (T.card:ℝ) ≤ (Real.log (n:ℝ))^k →
        (∀ i∈T, (n:ℝ)^(1/6+δ)≤D i ∧ D i≤n) →
        (∀ i∈T, ‖J i‖ ≤ C*(n:ℝ)*(Real.log (n:ℝ))^2*
          (n:ℝ)^(1/6:ℝ)/( (D i).totient:ℝ)) →
        ‖∑ i∈T, J i‖ ≤ ε*(n:ℝ) := by
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp hlim).eventually_ge_atTop 1,
    eventualLargeConductorWeight δ (k+2) (ε/(C+1)) hδ (by positivity)]
    with n hn hlog hweight
  intro T D J hcard hD hJ
  let L := Real.log (n:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  have hL1 : 1≤L := hlog
  have hL : 0 < L := by linarith
  have hpow : 0 < L^k := Real.rpow_pos_of_pos hL _
  have hLadd : L^(k+2) = L^k*L^2 := by rw [Real.rpow_add hL, Real.rpow_two]
  have hterm (i : ℕ) (hi : i∈T) :
      ‖J i‖ ≤ ε*(n:ℝ)/L^k := by
    obtain ⟨h₁,h₂⟩ := hD i hi
    have hw := hweight (D i) h₁ h₂
    change L^(k+2)*v/((D i).totient:ℝ) ≤ ε/(C+1) at hw
    rw [hLadd] at hw
    apply (le_div_iff₀ hpow).2
    calc
      ‖J i‖*L^k ≤ (C*(n:ℝ)*L^2*v/((D i).totient:ℝ))*L^k :=
        mul_le_mul_of_nonneg_right (hJ i hi) hpow.le
      _ = C*(n:ℝ)*(L^k*L^2*v/((D i).totient:ℝ)) := by ring
      _ ≤ C*(n:ℝ)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ ε*(n:ℝ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < C+1)).2
        nlinarith only [mul_nonneg hε.le (Nat.cast_nonneg n : (0:ℝ)≤n)]
  calc
    _ ≤ ∑ i∈T, ‖J i‖ := norm_sum_le _ _
    _ ≤ ∑ i∈T, ε*(n:ℝ)/L^k := sum_le_sum hterm
    _ = (T.card:ℝ)*(ε*(n:ℝ)/L^k) := by simp
    _ ≤ L^k*(ε*(n:ℝ)/L^k) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

end
end InnerFloorZeroModel
#print axioms InnerFloorZeroModel.continuousPacket_bound
#print axioms InnerFloorZeroModel.sparseLargePackets_o

/-!
The Gauss lifting lemmas below are extracted from the community's accepted
PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4, as stored in
alternate-signed/Type2B1B4Accepted.lean from the official main checkout.
Original proofs are retained; only the small necessary namespaces are used.
Apache-2.0 upstream license. This is a research-only standalone replay.
-/
open Finset
namespace RouteB_LargeSieve
open Complex Real
noncomputable section
def additivePhase (x : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * x)

theorem additivePhase_add (x y : ℝ) : additivePhase (x + y) = additivePhase x * additivePhase y := by
  dsimp [additivePhase]
  rw [circleMap_zero_mul, one_mul, mul_add]


end
end RouteB_LargeSieve
namespace RouteB_DyadicMixedB4DualCharacter
theorem sum_natCast_range_eq_zmod {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q] (f : ZMod q → R) :
    ∑ u ∈ range q, f (u : ZMod q) = ∑ z : ZMod q, f z := by
  apply sum_bij (s := range q) (t := (univ : Finset (ZMod q))) (fun u _ => (u : ZMod q))
  · simp
  · intro u uMember v vMember equal
    have valEqual := congrArg ZMod.val equal
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp uMember),
      Nat.mod_eq_of_lt (mem_range.mp vMember)] using valEqual
  · intro z _
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro u _
    rfl


end RouteB_DyadicMixedB4DualCharacter

section

open Finset RouteB_LargeSieve RouteB_DyadicMixedB4DualCharacter
open scoped Classical

namespace RouteB_DyadicMixedB4GaussLift

noncomputable section

theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (d f : ℕ) (F : ℕ → R) :
    ∑ x ∈ range (d * f), F x = ∑ j ∈ range f, ∑ a ∈ range d, F (d * j + a) := by
  induction f with
  | zero => simp
  | succ f ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem stdAddChar_nat_fraction {q : ℕ} [NeZero q] (k : ℕ) :
    ZMod.stdAddChar (k : ZMod q) = additivePhase ((k : ℝ) / q) := by
  rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
  unfold additivePhase
  rw [circleMap_zero, Complex.ofReal_one, one_mul]
  push_cast
  congr 1
  ring

theorem stdAddChar_mul_nat_fraction {q : ℕ} [NeZero q] (k a : ℕ) :
    ZMod.stdAddChar ((k : ZMod q) * (a : ZMod q)) = additivePhase ((k : ℝ) * a / q) := by
  rw [← Nat.cast_mul, stdAddChar_nat_fraction, Nat.cast_mul]

set_option maxHeartbeats 600000 in
theorem sum_phase_fraction_eq_if_dvd {q : ℕ} [NeZero q] (k : ℕ) :
    (∑ a ∈ range q, additivePhase ((k : ℝ) * a / q)) = if q ∣ k then (q : ℂ) else 0 := by
  simp_rw [← stdAddChar_mul_nat_fraction]
  rw [sum_natCast_range_eq_zmod (fun z => ZMod.stdAddChar ((k : ZMod q) * z))]
  simp_rw [mul_comm (k : ZMod q)]
  rw [AddChar.sum_mulShift (k : ZMod q) (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  have zeroIff : (k : ZMod q) = 0 ↔ q ∣ k := by rw [ZMod.natCast_eq_zero_iff]
  by_cases divides : q ∣ k
  · simp [divides, zeroIff.mpr divides]
  · have nonzero : (k : ZMod q) ≠ 0 := fun zero => divides (zeroIff.mp zero)
    simp [divides, nonzero]

theorem gaussSum_as_fraction_sum {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod d)) =
      ∑ a ∈ range d, χ (a : ZMod d) * additivePhase ((k : ℝ) * a / d) := by
  unfold gaussSum
  rw [← sum_natCast_range_eq_zmod]
  simp_rw [AddChar.mulShift_apply, stdAddChar_mul_nat_fraction]

set_option maxHeartbeats 600000 in
theorem lift_gaussSum {d f : ℕ} [NeZero d] [NeZero f]
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    (∑ u ∈ range (d * f), χ (u : ZMod d) * additivePhase ((k : ℝ) * u / ((d : ℝ) * f))) =
      if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
  have dNonzero : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have fNonzero : (f : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne f
  rw [sum_range_blocks, Finset.sum_comm]
  have liftEntry (a j : ℕ) :
      χ ((d * j + a : ℕ) : ZMod d) * additivePhase ((k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f)) =
        (χ (a : ZMod d) * additivePhase ((k : ℝ) * a / ((d : ℝ) * f))) *
          additivePhase ((k : ℝ) * j / f) := by
    have angle : (k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f) =
        (k : ℝ) * a / ((d : ℝ) * f) + (k : ℝ) * j / f := by
      push_cast
      field_simp
      ring
    rw [angle, additivePhase_add, ← mul_assoc]
    have same : ((d * j + a : ℕ) : ZMod d) = (a : ZMod d) := by push_cast; simp
    rw [same]
  simp_rw [liftEntry, ← mul_sum, sum_phase_fraction_eq_if_dvd]
  by_cases divisible : f ∣ k
  · simp only [if_pos divisible, ← Finset.sum_mul, gaussSum_as_fraction_sum]
    rw [mul_comm _ (f : ℂ)]
    apply congrArg (fun z : ℂ => (f : ℂ) * z)
    refine sum_congr rfl fun a _ => ?_
    have h : (k : ℝ) = ((k / f : ℕ) : ℝ) * f := by
      exact_mod_cast (Nat.div_mul_cancel divisible).symm
    have sameAngle : (k : ℝ) * a / ((d : ℝ) * f) = (((k / f : ℕ) : ℝ)) * a / d := by
      conv_lhs => rw [h]
      field_simp
    rw [sameAngle]
  · simp [divisible]


end
end RouteB_DyadicMixedB4GaussLift

end

section

open Finset ArithmeticFunction RouteB_LargeSieve RouteB_DyadicMixedB4GaussLift
open scoped ArithmeticFunction.Moebius Classical

namespace RouteB_DyadicMixedB4MoebiusGauss

noncomputable section

def moebiusComplex (m : ℕ) : ℂ := (μ m : ℂ)

theorem norm_moebiusComplex_le_one (m : ℕ) : ‖moebiusComplex m‖ ≤ 1 := by
  rw [moebiusComplex, Complex.norm_intCast]
  exact_mod_cast (abs_moebius_le_one (n := m))

theorem moebius_coprime_indicator {M : ℕ} (MPositive : 0 < M) (u : ℕ) :
    (∑ e ∈ M.divisors.filter (fun e => e ∣ u), moebiusComplex e) =
      if u.Coprime M then (1 : ℂ) else 0 := by
  let g := u.gcd M
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_right u MPositive
  have divisorsEquality : M.divisors.filter (fun e => e ∣ u) = g.divisors := by
    ext e
    rw [mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨eDividesM, _⟩, eDividesU⟩
      exact ⟨Nat.dvd_gcd eDividesU eDividesM, gPositive.ne'⟩
    · rintro ⟨eDividesG, _⟩
      exact ⟨⟨eDividesG.trans (Nat.gcd_dvd_right u M), MPositive.ne'⟩,
        eDividesG.trans (Nat.gcd_dvd_left u M)⟩
  have convolution : (∑ e ∈ g.divisors, μ e) = (1 : ArithmeticFunction ℤ) g := by
    rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta]
  rw [divisorsEquality]
  simp_rw [moebiusComplex, ← Int.cast_sum, convolution]
  change (((1 : ArithmeticFunction ℤ) g : ℤ) : ℂ) = if g = 1 then (1 : ℂ) else 0
  by_cases one : g = 1
  · simp [one, one_apply]
  · simp [one, one_apply]

theorem changeLevel_nat_indicator {d M : ℕ} (dDivides : d ∣ M) (χ : DirichletCharacter ℂ d)
    (u : ℕ) : DirichletCharacter.changeLevel dDivides χ (u : ZMod M) =
      (if u.Coprime M then (1 : ℂ) else 0) * χ (u : ZMod d) := by
  by_cases coprime : u.Coprime M
  · rw [if_pos coprime, one_mul]
    have same := DirichletCharacter.changeLevel_eq_cast_of_dvd χ dDivides (ZMod.unitOfCoprime u coprime)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast dDivides] at same
    exact same
  · rw [if_neg coprime, zero_mul]
    exact MulChar.map_nonunit _ (fun unit => coprime ((ZMod.isUnit_iff_coprime u M).mp unit))

theorem sum_filter_dvd_range {R : Type*} [AddCommMonoid R] {e M : ℕ}
    (ePositive : 0 < e) (eDivides : e ∣ M) (F : ℕ → R) :
    (∑ u ∈ (range M).filter (fun u => e ∣ u), F u) = ∑ v ∈ range (M / e), F (e * v) := by
  have quotient : e * (M / e) = M := Nat.mul_div_cancel' eDivides
  symm
  apply sum_bij (s := range (M / e)) (t := (range M).filter (fun u => e ∣ u)) (fun v _ => e * v)
  · intro v vMember
    refine mem_filter.mpr ⟨mem_range.mpr ?_, dvd_mul_right e v⟩
    rw [← quotient]
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp vMember) ePositive
  · intro v _ w _ eq
    exact Nat.eq_of_mul_eq_mul_left ePositive eq
  · intro u uMember
    obtain ⟨uRange, v, h⟩ := mem_filter.mp uMember
    refine ⟨v, mem_range.mpr ?_, h.symm⟩
    have prodLt : e * v < e * (M / e) := h ▸ quotient.symm ▸ mem_range.mp uRange
    exact Nat.lt_of_mul_lt_mul_left prodLt
  · intro v _
    rfl

theorem sum_inducedGauss_moebius {d M : ℕ} [NeZero M] (dDivides : d ∣ M)
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M)) =
      ∑ e ∈ M.divisors, moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) * additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) := by
  rw [gaussSum_as_fraction_sum]
  calc
    _ = ∑ u ∈ range M, ∑ e ∈ M.divisors.filter (fun e => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      refine sum_congr rfl fun u _ => ?_
      rw [changeLevel_nat_indicator, ← moebius_coprime_indicator (NeZero.pos M), mul_assoc, sum_mul]
    _ = ∑ e ∈ M.divisors, ∑ u ∈ (range M).filter (fun u => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun e eMember => ?_
      have eDivides := (Nat.mem_divisors.mp eMember).1
      have ePositive := Nat.pos_of_mem_divisors eMember
      have eNonzero : (e : ℝ) ≠ 0 := by exact_mod_cast ePositive.ne'
      have MNonzero : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
      have quotientNonzero : ((M / e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast quotientPositive.ne'
      have quotient : (M : ℝ) = e * ((M / e : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' eDivides).symm
      rw [sum_filter_dvd_range ePositive eDivides, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      have scales : (k : ℝ) * (e * v : ℕ) / M = (k : ℝ) * v / ((M / e : ℕ) : ℝ) := by
        push_cast
        rw [quotient]
        field_simp
      rw [scales, Nat.cast_mul, map_mul]
      ring


end
end RouteB_DyadicMixedB4MoebiusGauss

end

section

open Finset RouteB_DyadicMixedB4GaussLift RouteB_DyadicMixedB4MoebiusGauss
open scoped Classical

namespace RouteB_DyadicMixedB4ImprimitiveBound

noncomputable section

theorem norm_primitive_gauss_shift_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (primitive : χ.IsPrimitive) (x : ZMod d) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ ≤ Real.sqrt d := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar primitive, norm_mul,
    DirichletCharacter.norm_gaussSum_stdAddChar primitive]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (DirichletCharacter.norm_le_one _ _)

theorem conductor_cofactor {M d e : ℕ} [NeZero d] [NeZero M] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (coprime : e.Coprime d) :
    0 < M / e / d ∧ d * (M / e / d) = M / e ∧ e * (d * (M / e / d)) = M := by
  have eDivides := (Nat.mem_divisors.mp eMember).1
  have ePositive := Nat.pos_of_mem_divisors eMember
  have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
  have joint : e * d ∣ M := coprime.mul_dvd_of_dvd_of_dvd eDivides dDivides
  have dividesQuotient : d ∣ M / e := (Nat.dvd_div_iff_mul_dvd eDivides).mpr (by simpa [mul_comm] using joint)
  have quotient := Nat.mul_div_cancel' dividesQuotient
  exact ⟨Nat.div_pos (Nat.le_of_dvd quotientPositive dividesQuotient) (NeZero.pos d), quotient,
    by rw [quotient, Nat.mul_div_cancel' eDivides]⟩

theorem norm_induced_gauss_term {M d e : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (k : ℕ) {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) :
    ‖moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) *
          RouteB_LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ)))‖ ≤
      if e.Coprime d ∧ (M / e / d) ∣ k then ((M / e / d : ℕ) : ℝ) * Real.sqrt d else 0 := by
  by_cases coprime : e.Coprime d
  · obtain ⟨fPositive, hFactor, _⟩ := conductor_cofactor dDivides eMember coprime
    let f := M / e / d
    letI : NeZero f := ⟨fPositive.ne'⟩
    have liftIdentity : (∑ v ∈ range (M / e), χ (v : ZMod d) *
        RouteB_LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) =
        if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
      convert lift_gaussSum (f := f) χ k using 1
      rw [show (M / e : ℕ) = d * f from hFactor.symm, Nat.cast_mul]
    rw [liftIdentity]
    by_cases divides : f ∣ k
    · have divides' : (M / e / d) ∣ k := divides
      have relevant : e.Coprime d ∧ (M / e / d) ∣ k := ⟨coprime, divides'⟩
      simp only [if_pos divides, if_pos relevant, norm_mul, Complex.norm_natCast]
      have factor : ‖moebiusComplex e‖ * ‖χ (e : ZMod d)‖ ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)).trans
          (by simpa only [mul_one] using norm_moebiusComplex_le_one e)
      refine (mul_le_of_le_one_left (by positivity) factor).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_primitive_gauss_shift_le primitive _) (Nat.cast_nonneg _)
    · have divides' : ¬(M / e / d) ∣ k := divides
      simp [divides, divides', coprime]
  · have valZero : χ (e : ZMod d) = 0 := MulChar.map_nonunit _
      (fun h => coprime ((ZMod.isUnit_iff_coprime e d).mp h))
    simp [coprime, valZero]

theorem norm_induced_gauss_le {M d : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M))‖ ≤
      Real.sqrt d * ∑ f ∈ k.divisors.filter (fun f => d * f ∣ M), (f : ℝ) := by
  let cof (e : ℕ) := M / e / d
  let support := M.divisors.filter (fun e => e.Coprime d ∧ cof e ∣ k)
  let bound := k.divisors.filter (fun f => d * f ∣ M)
  have imageSubset : support.image cof ⊆ bound := by
    intro f member
    obtain ⟨e, eMember, rfl⟩ := mem_image.mp member
    obtain ⟨divisor, coprime, divides⟩ := mem_filter.mp eMember
    obtain ⟨_, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides, kPositive.ne'⟩,
      ⟨e, by rw [mul_comm]; exact identity.symm⟩⟩
  have injectiveOn : Set.InjOn cof (support : Set ℕ) := by
    intro e eMember e' e'Member same
    obtain ⟨divisor, coprime, _⟩ := mem_filter.mp eMember
    obtain ⟨divisor', coprime', _⟩ := mem_filter.mp e'Member
    obtain ⟨fPositive, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    obtain ⟨_, _, identity'⟩ := conductor_cofactor dDivides divisor' coprime'
    change e * (d * cof e) = M at identity
    change e' * (d * cof e') = M at identity'
    rw [← same] at identity'
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (NeZero.pos d) fPositive) (identity.trans identity'.symm)
  have sumBound : (∑ e ∈ support, (cof e : ℝ)) ≤ ∑ f ∈ bound, (f : ℝ) := by
    rw [← sum_image injectiveOn]
    exact sum_le_sum_of_subset_of_nonneg imageSubset fun _ _ _ => Nat.cast_nonneg _
  rw [sum_inducedGauss_moebius]
  refine (norm_sum_le _ _).trans ?_
  have boundTerms := sum_le_sum (s := M.divisors)
    (fun e member => norm_induced_gauss_term dDivides member k primitive)
  refine boundTerms.trans ?_
  change (∑ e ∈ M.divisors, if e.Coprime d ∧ cof e ∣ k then (cof e : ℝ) * Real.sqrt d else 0) ≤
    Real.sqrt d * ∑ f ∈ bound, (f : ℝ)
  rw [← sum_filter, ← sum_mul, mul_comm (Real.sqrt d)]
  exact mul_le_mul_of_nonneg_right sumBound (Real.sqrt_nonneg _)


end
end RouteB_DyadicMixedB4ImprimitiveBound

end

open Finset RouteB_DyadicMixedB4ImprimitiveBound
namespace RouteB_DyadicMixedB4CharacterFactorBound
noncomputable section
theorem norm_dirichlet_gauss_induced {r q : ℕ} [NeZero r] [NeZero q] (rDivides : r ∣ q)
    (χ : DirichletCharacter ℂ r) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel rDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod q))‖ ≤
      Real.sqrt χ.conductor * ∑ f ∈ k.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ) := by
  have conductorNonzero : χ.conductor ≠ 0 := fun zero => NeZero.ne r
    (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp zero)
  letI : NeZero χ.conductor := ⟨conductorNonzero⟩
  have inductionBound := norm_induced_gauss_le (χ.conductor_dvd_level.trans rDivides)
    χ.primitiveCharacter_isPrimitive k kPositive
  rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level rDivides,
    DirichletCharacter.changeLevel_primitiveCharacter] at inductionBound
  exact inductionBound

theorem norm_dirichlet_gauss_standard {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt χ.conductor := by
  have induced := norm_dirichlet_gauss_induced (dvd_refl r) χ 1 (by decide)
  have onlyOne : ((1 : ℕ).divisors.filter (fun f => χ.conductor * f ∣ r)) = {1} := by
    ext f
    simp only [Nat.divisors_one, mem_filter, mem_singleton]
    constructor
    · exact And.left
    · rintro rfl
      exact ⟨rfl, by simpa only [mul_one] using χ.conductor_dvd_level⟩
  rw [onlyOne] at induced
  simpa [DirichletCharacter.changeLevel_self, AddChar.mulShift_one] using induced

end
end RouteB_DyadicMixedB4CharacterFactorBound

namespace InnerFloorGaussPacket
open Finset AddChar Complex
open scoped Classical ComplexConjugate
open RouteB_DyadicMixedB4CharacterFactorBound
noncomputable section
set_option maxHeartbeats 2000000
variable {q : ℕ} [NeZero q]

/-- The exact additiveWeight used in the accepted canonical zero correction. -/
def canonicalWeight (a : ZMod q) (χ : DirichletCharacter ℂ q) : ℂ :=
  conj (∑ r : ZMod q, conj (ZMod.stdAddChar (a*r))*χ r) / (q.totient:ℂ)

theorem canonicalWeight_eq (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    canonicalWeight (a:ZMod q) χ =
      χ (a:ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar / (q.totient:ℂ) := by
  unfold canonicalWeight
  have he : conj (∑ r : ZMod q, conj (ZMod.stdAddChar ((a:ZMod q)*r))*χ r) =
      gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (a:ZMod q)) := by
    rw [map_sum,gaussSum]
    apply sum_congr rfl
    intro r _
    rw [map_mul]
    change star (star (ZMod.stdAddChar ((a:ZMod q)*r))) * star (χ r) = _
    rw [star_star,MulChar.star_apply',AddChar.mulShift_apply,mul_comm]
  rw [he,gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar a,inv_inv]

theorem canonicalWeight_norm (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    ‖canonicalWeight (a:ZMod q) χ‖ ≤ Real.sqrt χ.conductor/(q.totient:ℝ) := by
  rw [canonicalWeight_eq,norm_div,norm_mul,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at h
  exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans h

/-- Signed coefficient at an arbitrary real shift. A phase need only have
norm at most one; no independence or favourable sign is assumed. -/
def canonicalPairCoefficient (χ ψ : DirichletCharacter ℂ q)
    (phase : (ZMod q)ˣ → ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ, canonicalWeight (a:ZMod q) χ *
    canonicalWeight (a:ZMod q) ψ * phase a

theorem canonicalPairCoefficient_bound (χ ψ : DirichletCharacter ℂ q)
    (phase : (ZMod q)ˣ → ℂ) (hp : ∀ a, ‖phase a‖ ≤ 1) :
    ‖canonicalPairCoefficient χ ψ phase‖ ≤
      Real.sqrt χ.conductor * Real.sqrt ψ.conductor / (q.totient:ℝ) := by
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  unfold canonicalPairCoefficient
  calc
    _ ≤ ∑ a : (ZMod q)ˣ, ‖canonicalWeight (a:ZMod q) χ *
        canonicalWeight (a:ZMod q) ψ * phase a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ,
        (Real.sqrt χ.conductor/(q.totient:ℝ))*
        (Real.sqrt ψ.conductor/(q.totient:ℝ)) := by
      apply sum_le_sum
      intro a _
      rw [norm_mul,norm_mul]
      calc
        _ ≤ ‖canonicalWeight (a:ZMod q) χ‖ * ‖canonicalWeight (a:ZMod q) ψ‖ :=
          mul_le_of_le_one_right (by positivity) (hp a)
        _ ≤ _ := mul_le_mul (canonicalWeight_norm a χ) (canonicalWeight_norm a ψ)
          (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [sum_const,Finset.card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul]
      field_simp

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.canonicalWeight_eq
#print axioms InnerFloorGaussPacket.canonicalWeight_norm
#print axioms InnerFloorGaussPacket.canonicalPairCoefficient_bound

namespace InnerFloorGaussPacket
open Finset AddChar Complex RouteB_InnerFloorLinearTotient InnerFloorZeroModel
open scoped Classical ComplexConjugate
noncomputable section
set_option maxHeartbeats 2000000

variable {q : ℕ} [NeZero q]

theorem signedPair_eq (χ ψ : DirichletCharacter ℂ q) (n : ZMod q) :
    canonicalPairCoefficient χ ψ
      (fun a => ZMod.stdAddChar (-n*(a:ZMod q))) =
      (gaussSum χ⁻¹ ZMod.stdAddChar * gaussSum ψ⁻¹ ZMod.stdAddChar /
        (q.totient:ℂ)^2) *
        gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-n)) := by
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold canonicalPairCoefficient
  simp_rw [canonicalWeight_eq]
  have ht (a : (ZMod q)ˣ) :
      (χ (a:ZMod q)*gaussSum χ⁻¹ ZMod.stdAddChar/(q.totient:ℂ)) *
        (ψ (a:ZMod q)*gaussSum ψ⁻¹ ZMod.stdAddChar/(q.totient:ℂ)) *
          ZMod.stdAddChar (-n*(a:ZMod q)) =
      (gaussSum χ⁻¹ ZMod.stdAddChar * gaussSum ψ⁻¹ ZMod.stdAddChar /
        (q.totient:ℂ)^2) *
        ((χ*ψ) (a:ZMod q)*ZMod.stdAddChar (-n*(a:ZMod q))) := by
    rw [MulChar.mul_apply]
    field_simp
    <;> ring
  simp_rw [ht,← Finset.mul_sum]
  congr 1
  let F : ZMod q → ℂ := fun a => (χ*ψ) a * ZMod.stdAddChar (-n*a)
  change (∑ a : (ZMod q)ˣ, F (a:ZMod q)) = ∑ a : ZMod q, F a
  let S := (Finset.univ : Finset (ZMod q)).filter IsUnit
  have hS : (∑ a : (ZMod q)ˣ, F (a:ZMod q)) = ∑ a∈S, F a := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
      (t := S) (fun a _ => (a : ZMod q))
    · intro a _
      simp [S,a.isUnit]
    · intro a _ b _ h
      exact Units.ext h
    · intro a ha
      have hu : IsUnit a := by simpa [S] using ha
      exact ⟨hu.unit,Finset.mem_univ _,hu.unit_spec⟩
    · intro a _
      rfl
  rw [hS]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hnot
  have hn : ¬ IsUnit a := by simpa [S] using hnot
  dsimp [F]
  simp [MulChar.map_nonunit _ hn]

/-- The common modulus is a multiple of the LCM of the primitive levels.
All coefficients are those of the actual finite additiveWeight expansion. -/
theorem liftedContinuousPacket_bound {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    (χ : DirichletCharacter ℂ d₁) (ψ : DirichletCharacter ℂ d₂)
    (L M : ℕ) (hL : 0 < L) (h₁ : d₁∣L) (h₂ : d₂∣L)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 M)
    (U X β₁ γ₁ β₂ γ₂ : ℝ) (hU : 0≤U) (hX : 0≤X)
    (hβ₁ : 1/2≤β₁) (hβ₂ : 1/2≤β₂) (n : ℕ) :
    let a (m : ℕ) : ℂ :=
      if hm : 0 < m then
        letI : NeZero (L*m) := ⟨(Nat.mul_pos hL hm).ne'⟩
        canonicalPairCoefficient
          (DirichletCharacter.changeLevel (h₁.trans (dvd_mul_right L m)) χ)
          (DirichletCharacter.changeLevel (h₂.trans (dvd_mul_right L m)) ψ)
          (fun a => ZMod.stdAddChar (-(n:ZMod (L*m))*(a:ZMod (L*m))))
      else 0
    ‖(X:ℂ)*(∑ m∈S, a m * pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ)))‖ ≤
      8*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  dsimp only
  let g := Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ)
  have hg : 0≤g := by dsimp [g]; positivity
  have hgL : g≤(L:ℝ) := by
    calc
      g ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul
          (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hL h₁))
          (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hL h₂))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  apply continuousPacket_bound S M L hL hS g U X β₁ γ₁ β₂ γ₂ hg hgL hU hX hβ₁ hβ₂
  intro m hm
  have hm0 : 0 < m := (mem_Icc.mp (hS hm)).1
  rw [dif_pos hm0]
  letI : NeZero (L*m) := ⟨(Nat.mul_pos hL hm0).ne'⟩
  have h := canonicalPairCoefficient_bound
    (DirichletCharacter.changeLevel (h₁.trans (dvd_mul_right L m)) χ)
    (DirichletCharacter.changeLevel (h₂.trans (dvd_mul_right L m)) ψ)
    (fun a => ZMod.stdAddChar (-(n:ZMod (L*m))*(a:ZMod (L*m))))
    (fun a => by
      have hu := AddChar.norm_apply (ZMod.stdAddChar (N := L*m))
        (-(n:ZMod (L*m))*(a:ZMod (L*m)))
      exact hu.le)
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel] at h
  apply h.trans
  unfold g
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos d₁) χ.conductor_dvd_level))
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos d₂) ψ.conductor_dvd_level))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.signedPair_eq
#print axioms InnerFloorGaussPacket.liftedContinuousPacket_bound
/-! Plancherel bridge adapted from ShortProgressionsMeanTheta (#3789),
and the verified InnerFloorPhysicalL2 research module. -/
section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in


private theorem test_fourier_swap {f : ℝ → ℂ} (hf : Integrable f) (g : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 f) x • g x) = ∫ x, f x • (𝓕 g) x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf g.integrable
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem ae_eq_of_schwartz_test {u v : ℝ → ℂ}
    (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume)
    (h : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * u x) = ∫ x, φ x * v x) :
    u =ᵐ[volume] v := by
  apply ae_eq_of_integral_contDiff_smul_eq hu hv
  intro g hg hgc
  let φ := (hgc.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  simp only [RCLike.real_smul_eq_coe_mul]
  exact h φ
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem lp_test (v : Lp ℂ 2 (volume : Measure ℝ)) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 φ) x • v x) = ∫ x, φ x • (𝓕 v) x := calc
  _ = Lp.toTemperedDistribution v (𝓕 φ) := (Lp.toTemperedDistribution_apply ..).symm
  _ = (𝓕 (Lp.toTemperedDistribution v)) φ := rfl
  _ = Lp.toTemperedDistribution (𝓕 v) φ := by rw [Lp.fourier_toTemperedDistribution_eq]
  _ = _ := Lp.toTemperedDistribution_apply ..
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem fourier_agrees {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  let v := h₂.toLp f
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_schwartz_test hc.locallyIntegrable
    ((Lp.memLp (𝓕 v)).locallyIntegrable (by norm_num))
  intro φ
  have A := test_fourier_swap (f := f) h₁ φ
  have B := lp_test v φ
  simp only [smul_eq_mul] at A B
  have C : (∫ x : ℝ, f x * (𝓕 φ) x) = ∫ x : ℝ, (𝓕 φ) x * v x := by
    apply integral_congr_ae
    filter_upwards [h₂.coeFn_toLp] with x hx
    change f x * (𝓕 φ) x = (𝓕 φ) x * (h₂.toLp f) x
    rw [hx, mul_comm]
  have D : (∫ x : ℝ, φ x * (𝓕 f) x) = ∫ x : ℝ, (𝓕 f) x * φ x :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm ..)
  exact D.trans (A.trans (C.trans B))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem lp_energy (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ x, ‖f x‖^2 = ‖f‖^2 := by
  conv_rhs => rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  exact integral_congr_ae (ae_of_all _ fun x => norm_sq_eq_re_inner (𝕜 := ℂ) (f x))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem box_plancherel {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    Integrable (fun ξ => ‖𝓕 f ξ‖^2) ∧ (∫ ξ, ‖𝓕 f ξ‖^2) = ∫ x, ‖f x‖^2 := by
  let v := h₂.toLp f
  have he := fourier_agrees h₁ h₂
  have hae : (fun ξ => ‖𝓕 f ξ‖^2) =ᵐ[volume] (fun ξ => ‖(𝓕 v) ξ‖^2) := by
    filter_upwards [he] with ξ h using congrArg (fun z : ℂ => ‖z‖^2) h
  refine ⟨((Lp.memLp (𝓕 v)).norm.integrable_sq).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, lp_energy, Lp.norm_fourier_eq, ← lp_energy]
  apply integral_congr_ae
  filter_upwards [h₂.coeFn_toLp] with x h using congrArg (fun z : ℂ => ‖z‖^2) h

def zeroKernel (β γ : ℝ) : ℝ → ℂ :=
  (Set.Ioc (0:ℝ) 1).indicator (fun x => (x^(β-1):ℝ) • phase (γ*Real.log x))

private theorem kernel_norm_eq (β γ : ℝ) :
    (fun x => ‖zeroKernel β γ x‖) =
      (Set.Ioc (0:ℝ) 1).indicator (fun x => x^(β-1)) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
  · rw [zeroKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx,norm_smul,norm_phase,
      mul_one,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
  · simp [zeroKernel,Set.indicator_of_notMem hx]

private theorem kernel_sq_eq (β γ : ℝ) :
    (fun x => ‖zeroKernel β γ x‖^2) =
      (Set.Ioc (0:ℝ) 1).indicator (fun x => x^(2*β-2)) := by
  funext x
  have hn := congrFun (kernel_norm_eq β γ) x
  rw [hn]
  by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx,
      ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    congr 1
    norm_num
    ring
  · simp [Set.indicator_of_notMem hx]

private theorem kernel_integrable (β γ : ℝ) (hβ : 0 < β) :
    Integrable (zeroKernel β γ) := by
  have hm : Measurable (zeroKernel β γ) := by
    unfold zeroKernel
    apply Measurable.indicator _ measurableSet_Ioc
    unfold phase
    fun_prop
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  rw [kernel_norm_eq,integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β-1)).1

private theorem kernel_memLp (β γ : ℝ) (hβ : 1/2 < β) :
    MemLp (zeroKernel β γ) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (kernel_integrable β γ (by linarith)).aestronglyMeasurable).mpr
  rw [kernel_sq_eq,integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 2*β-2)).1

private theorem kernel_energy (β γ : ℝ) (hβ : 1/2 < β) :
    ∫ x, ‖zeroKernel β γ x‖^2 = 1/(2*β-1) := by
  rw [kernel_sq_eq,integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
    integral_rpow (Or.inl (by linarith : -1 < 2*β-2))]
  rw [show 2*β-2+1=2*β-1 by ring,Real.one_rpow,
    Real.zero_rpow (by linarith : 2*β-1≠0),sub_zero]

private theorem transform_fourier (β γ v : ℝ) :
    transform β γ v = 𝓕 (zeroKernel β γ) (-v) := by
  rw [Real.fourier_real_eq_integral_exp_smul,transform,
    intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
  have he : (fun x => Complex.exp (↑(-2*Real.pi*x*(-v))*Complex.I) • zeroKernel β γ x) =
    (Set.Ioc (0:ℝ) 1).indicator (fun x => (x^(β-1):ℝ) • phase (γ*Real.log x+2*Real.pi*v*x)) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
    · rw [zeroKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx]
      simp only [smul_eq_mul,phase,Complex.ofReal_add,add_mul,Complex.exp_add,
        RCLike.real_smul_eq_coe_mul]
      rw [show (-2*Real.pi*x*(-v)) = 2*Real.pi*v*x by ring]
      ring
    · simp [zeroKernel,Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Ioc]

theorem transform_energy (β γ : ℝ) (hβ : 1/2 < β) :
    Integrable (fun v => ‖transform β γ v‖^2) ∧
      (∫ v, ‖transform β γ v‖^2) = 1/(2*β-1) := by
  obtain ⟨hi,he⟩ := box_plancherel (kernel_integrable β γ (by linarith))
    (kernel_memLp β γ hβ)
  simp_rw [transform_fourier]
  constructor
  · simpa only [neg_one_mul] using hi.comp_mul_left' (by norm_num : (-1:ℝ)≠0)
  · calc
      _ = (∫ v, ‖𝓕 (zeroKernel β γ) v‖^2) := by
        have h := Measure.integral_comp_mul_left (fun v => ‖𝓕 (zeroKernel β γ) v‖^2) (-1:ℝ)
        simpa [neg_one_mul] using h
      _ = _ := he.trans (kernel_energy β γ hβ)


/-- The absolute integral of a pair is uniformly bounded at every cutoff,
including the long inner arcs. No hypothesis on the imaginary parts. -/
theorem pairIntegral_uniform (β₁ γ₁ β₂ γ₂ R : ℝ)
    (h₁ : 3/4≤β₁) (h₂ : 3/4≤β₂) (hR : 0≤R) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ R‖ ≤ 2 := by
  obtain ⟨hi₁,he₁⟩ := transform_energy β₁ γ₁ (by linarith)
  obtain ⟨hi₂,he₂⟩ := transform_energy β₂ γ₂ (by linarith)
  let f (v : ℝ) := (‖transform β₁ γ₁ v‖^2+‖transform β₂ γ₂ v‖^2)/2
  have hf : Integrable f := (hi₁.add hi₂).div_const 2
  have hp (v : ℝ) :
      ‖transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v))‖ ≤ f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    dsimp [f]
    nlinarith [sq_nonneg (‖transform β₁ γ₁ v‖-‖transform β₂ γ₂ v‖)]
  have hA : ∀ v, 0≤f v := by intro v;dsimp [f];positivity
  unfold pairIntegral
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R,
      ‖transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R, f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hf.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v, f v := setIntegral_le_integral hf (Filter.Eventually.of_forall hA)
    _ = (1/(2*β₁-1)+1/(2*β₂-1))/2 := by
      dsimp [f]
      rw [integral_div,integral_add hi₁ hi₂,he₁,he₂]
    _ ≤ 2 := by
      have hb₁ : 1/(2*β₁-1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
      have hb₂ : 1/(2*β₂-1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
      linarith

end
end InnerFloorZeroModel
#print axioms InnerFloorZeroModel.transform_energy

#print axioms InnerFloorZeroModel.pairIntegral_uniform
end

namespace RouteB_DyadicMixedB4CharacterFactorBound
noncomputable section
theorem norm_gauss_neg_shift_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-x))‖ ≤ ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ := by
  have equality : ZMod.stdAddChar.mulShift (-x) =
      (ZMod.stdAddChar.mulShift x).mulShift ((-1 : (ZMod q)ˣ) : ZMod q) := by
    ext y
    simp [AddChar.mulShift_apply, mul_assoc]
  rw [equality, gaussSum_mulShift_eq χ (ZMod.stdAddChar.mulShift x) (-1), norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)


end
end RouteB_DyadicMixedB4CharacterFactorBound

open RouteB_InnerFloorLinearTotient

/-!
A product-conductor saving for arbitrary shifts, including noncoprime
shifts. The low-product-conductor packet is kept separate.
-/
open Finset
open scoped Classical
open RouteB_DyadicMixedB4CharacterFactorBound
namespace RouteB_InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem divisorSum_le_log (m : ℕ) (hm : 0 < m) :
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
    (n : ℕ) (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt χ.conductor := by
  let d := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hdp
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hmp
  have hqR : (q:ℝ)=(d:ℝ)*(m:ℝ) := by exact_mod_cast hm
  have hsub : n.divisors.filter (fun f => d*f ∣ q) ⊆ m.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left hdp hdiv,hmp.ne'⟩
  have hmq : m ≤ q := by
    rw [hm]
    exact Nat.le_mul_of_pos_left _ hdp
  have hlog : Real.log m≤Real.log q :=
    Real.log_le_log hmR (by exact_mod_cast hmq)
  have hs : (Real.sqrt (d:ℝ))^2=(d:ℝ) := Real.sq_sqrt hdR.le
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 hdR
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f ∣ q),(f:ℝ)) :=
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
      calc
        _ = (Real.sqrt (d:ℝ))^2 * ((m:ℝ)*(1+Real.log q)) := by ring
        _ = (d:ℝ)*((m:ℝ)*(1+Real.log q)) := by rw [hs]
        _ = _ := by rw [hqR]; ring

/-- The high-product-conductor part of the signed quadratic form has a
uniform square-root saving, independent of gcd(n,q). -/
theorem highProductConductorPacketBound
    (n : ℕ) (hn : 0 < n) (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) (hD : 0 < D) :
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
end RouteB_InnerFloorResearch

open RouteB_InnerFloorLinearTotient

/-!
Aggregate high-product-conductor weights over all common multiples.
Only finite arithmetic and the verified Gauss bound are used.
-/
open Finset RouteB_InnerFloorLinearTotient
open scoped Classical
namespace RouteB_InnerFloorResearch
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
  · have hA : 0 < A := hL.trans_le hLA
    have hlogA : 0≤Real.log A := Real.log_nonneg (by exact_mod_cast hA)
    let C := weightConstant*(1+Real.log A)^2/Real.sqrt D
    have hC : 0≤C := by
      dsimp [C]
      exact div_nonneg (mul_nonneg weightConstant_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
    have ht (q : ℕ) (hq : q∈(Icc 1 A).filter (fun q => L ∣ q)) :
        productCoefficient q d₁ d₂ D ≤ C*((L:ℝ)/(q.totient:ℝ)) := by
      have hq1 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
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
end RouteB_InnerFloorResearch

open RouteB_InnerFloorLinearTotient

/-!
Retain both the product conductor and the gcd of the shift with the
imprimitive part of the modulus. All estimates are unconditional.
-/
open Finset RouteB_DyadicMixedB4CharacterFactorBound
open scoped Classical
namespace RouteB_InnerFloorResearch
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
  have hl : Real.log (g:ℝ) ≤ Real.log (q:ℝ) :=
    Real.log_le_log (by exact_mod_cast hgp) (by exact_mod_cast hgq)
  calc
    _ ≤ Real.sqrt χ.conductor*(g:ℝ)*(1+Real.log g) :=
      shiftedGauss_gcdBound χ n hn
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hD))
          (by exact_mod_cast hgg' : (g:ℝ) ≤ (Nat.gcd n q:ℝ)) (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
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


/-- Interpolating the product conductor and gcd bounds eliminates the
conductor altogether. The ratio gcd(n,q)/q is the precise obstruction. -/
theorem shiftedGauss_geometricGcd (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q) := by
  let d := χ.conductor
  have hd : 0 < d := Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos q)
  have hs : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hL : 0 ≤ 1+Real.log q := by
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    linarith [Real.log_nonneg hq1]
  let a := ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖
  have ha : 0≤a := norm_nonneg _
  have h₁ : a ≤ (q:ℝ)*(1+Real.log q)/Real.sqrt d :=
    shiftedGauss_productConductor χ n hn
  have h₂ : a ≤ Real.sqrt d*(Nat.gcd n q:ℝ)*(1+Real.log q) :=
    shiftedGauss_smallProduct χ n d hn le_rfl
  have hsq : a^2 ≤ ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q)^2 := by
    calc
      _ = a*a := by ring
      _ ≤ ((q:ℝ)*(1+Real.log q)/Real.sqrt d)*
          (Real.sqrt d*(Nat.gcd n q:ℝ)*(1+Real.log q)) :=
        mul_le_mul h₁ h₂ ha (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hL) hs.le)
      _ = _ := by field_simp [hs.ne'] <;> ring
  have hroot : (Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ)))^2 =
      (q:ℝ)*(Nat.gcd n q:ℝ) := Real.sq_sqrt (by positivity)
  have hb : 0≤Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q) :=
    mul_nonneg (Real.sqrt_nonneg _) hL
  have hsq' : a^2 ≤ (Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q))^2 := by
    rw [mul_pow,hroot]
    exact hsq
  change a ≤ _
  nlinarith only [hsq',ha,hb]

/-- The fraction of a modulus accounted for by gcd(n,q) cannot increase
when q is replaced by a multiple. -/
theorem gcdRatio_mono_multiple (n L q : ℕ) (hn : 0 < n) (hL : 0 < L)
    (hLq : L ∣ q) (hq : 0 < q) :
    (Nat.gcd n q:ℝ)/(q:ℝ) ≤ (Nat.gcd n L:ℝ)/(L:ℝ) := by
  obtain ⟨m,hm⟩ := hLq
  have hmpos : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm,hm0,mul_zero] at hq
    omega
  let d := Nat.gcd n q
  have hd : d ∣ L*m := by rw [← hm]; exact Nat.gcd_dvd_right _ _
  have hsplit : d ∣ d.gcd L * d.gcd m := by
    simpa only [Nat.gcd_comm] using (Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr hd)
  have h₁ : d.gcd L ∣ Nat.gcd n L :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left n q))
      (Nat.gcd_dvd_right _ _)
  have h₂ : d.gcd m ∣ m := Nat.gcd_dvd_right _ _
  have hdiv : d ∣ Nat.gcd n L*m := hsplit.trans (Nat.mul_dvd_mul h₁ h₂)
  have hle : d ≤ Nat.gcd n L*m :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hn) hmpos) hdiv
  have hd' : (d:ℝ) ≤ (Nat.gcd n L:ℝ)*(m:ℝ) := by exact_mod_cast hle
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hm' : (q:ℝ)=(L:ℝ)*(m:ℝ) := by exact_mod_cast hm
  apply (div_le_div_iff₀ hq' hL').2
  calc
    _ ≤ ((Nat.gcd n L:ℝ)*(m:ℝ))*(L:ℝ) :=
      mul_le_mul_of_nonneg_right hd' hL'.le
    _ = _ := by rw [hm']; ring


end
end RouteB_InnerFloorResearch

namespace InnerFloorGaussPacket
open Finset RouteB_InnerFloorLinearTotient RouteB_InnerFloorResearch InnerFloorZeroModel
open RouteB_DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
variable {q : ℕ} [NeZero q]

def signedCoefficient (χ ψ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  canonicalPairCoefficient χ ψ (fun a => ZMod.stdAddChar (-(n:ZMod q)*(a:ZMod q)))

/-- Isolate the conductor factors of the two actual Fourier weights.
The third Gauss sum retains the signed information. -/
theorem signedCoefficient_norm_le (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖signedCoefficient χ ψ n‖ ≤
      Real.sqrt χ.conductor * Real.sqrt ψ.conductor *
        ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ /
          (q.totient:ℝ)^2 := by
  have h₁ := norm_dirichlet_gauss_standard χ⁻¹
  have h₂ := norm_dirichlet_gauss_standard ψ⁻¹
  rw [DirichletCharacter.conductor_inv] at h₁ h₂
  rw [signedCoefficient,signedPair_eq,norm_mul,norm_div,norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (Real.sqrt χ.conductor * Real.sqrt ψ.conductor / (q.totient:ℝ)^2) *
        ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul h₁ h₂ (norm_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

/-- Real high-product-conductor estimate with no coprimality restriction. -/
theorem signedCoefficient_highProduct (χ ψ : DirichletCharacter ℂ q)
    (n D : ℕ) (hn : 0 < n) (hDpos : 0 < D) (hD : D ≤ (χ*ψ).conductor) :
    ‖signedCoefficient χ ψ n‖ ≤ productCoefficient q χ.conductor ψ.conductor D := by
  apply (signedCoefficient_norm_le χ ψ n).trans
  unfold productCoefficient
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hlog : 0≤1+Real.log q := by linarith [Real.log_nonneg hq]
  have h := shiftedGauss_productConductor (χ*ψ) n hn
  have hden : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hDpos)
  have hshift : ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt D :=
    h.trans (div_le_div_of_nonneg_left (by positivity) hden
      (Real.sqrt_le_sqrt (by exact_mod_cast hD)))
  calc
    _ ≤ Real.sqrt χ.conductor*Real.sqrt ψ.conductor*
        ((q:ℝ)*(1+Real.log q)/Real.sqrt D)/(q.totient:ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hshift (by positivity)) (sq_nonneg _)
    _ = _ := by ring

end
end InnerFloorGaussPacket

#print axioms InnerFloorGaussPacket.signedCoefficient_norm_le
#print axioms InnerFloorGaussPacket.signedCoefficient_highProduct

namespace InnerFloorGaussPacket
open Finset RouteB_InnerFloorLinearTotient RouteB_InnerFloorResearch InnerFloorZeroModel
open RouteB_DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

/-- Uniform product conductor under common lift. -/
theorem productConductor_changeLevel {L q : ℕ} [NeZero L] [NeZero q]
    (h : L∣q) (χ ψ : DirichletCharacter ℂ L) :
    (DirichletCharacter.changeLevel h χ * DirichletCharacter.changeLevel h ψ).conductor =
      (χ*ψ).conductor := by
  rw [← map_mul,DirichletCharacter.conductor_changeLevel]

/-- A finite common-multiple sum of the genuine signed coefficients times
continuous zero-pair integrals. Large product conductor gives a saving
even when the individual primitive levels are small. -/
theorem highProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (β₁ γ₁ β₂ γ₂ : ℝ) (hβ₁ : 3/4≤β₁) (hβ₂ : 3/4≤β₂)
    (R : ℕ→ℝ) (hR : ∀ q∈S,0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * pairIntegral β₁ γ₁ β₂ γ₂ (R q)‖ ≤
      2*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  dsimp only
  let c (q : ℕ) := productCoefficient q χ.conductor ψ.conductor D
  have hc (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ c q := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    have hq0 : 0 < q := (mem_Icc.mp hqR).1
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨hq0.ne'⟩
    have hp : D ≤ (DirichletCharacter.changeLevel hqL χ *
          DirichletCharacter.changeLevel hqL ψ).conductor := by
      rw [productConductor_changeLevel]
      exact hprod
    have h := signedCoefficient_highProduct
      (DirichletCharacter.changeLevel hqL χ) (DirichletCharacter.changeLevel hqL ψ) n D hn hD hp
    simpa only [c,DirichletCharacter.conductor_changeLevel] using h
  have hS' : S ⊆ (Icc 1 A).filter (fun q => χ.conductor∣q ∧ ψ.conductor∣q) := by
    intro q hq
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    exact mem_filter.mpr ⟨hqR,χ.conductor_dvd_level.trans hqL,ψ.conductor_dvd_level.trans hqL⟩
  have hsum : ∑ q∈S,c q ≤ weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
    apply (sum_le_sum_of_subset_of_nonneg hS' (fun q hq _ => ?_)).trans
      (productCoefficientFamily A χ.conductor ψ.conductor D
        (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos L))
        (Nat.pos_of_dvd_of_pos ψ.conductor_dvd_level (NeZero.pos L)) hD)
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq0
    have hlog := Real.log_nonneg hq1
    unfold productCoefficient
    positivity
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        pairIntegral β₁ γ₁ β₂ γ₂ (R q)‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S,c q*2 := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hc q hq) (pairIntegral_uniform β₁ γ₁ β₂ γ₂ (R q) hβ₁ hβ₂ (hR q hq))
        (norm_nonneg _) ((norm_nonneg _).trans (hc q hq))
    _ ≤ _ := by
      rw [← sum_mul]
      calc
        _ ≤ (weightConstant^3*(1+Real.log A)^4/Real.sqrt D)*2 :=
          mul_le_mul_of_nonneg_right hsum (by norm_num)
        _ = _ := by ring

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.productConductor_changeLevel
#print axioms InnerFloorGaussPacket.highProduct_sum

section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
/-- Exactly the trapezoid used in the accepted canonical explicit formula. -/
def dyadicTaper (a b x : ℝ) : ℝ := max 0 (min (x-a) (min 1 (b+1-x)))

theorem dyadicTaper_bounds (a b x : ℝ) :
    0 ≤ dyadicTaper a b x ∧ dyadicTaper a b x ≤ 1 := by
  unfold dyadicTaper
  exact ⟨le_max_left _ _,max_le (by norm_num) ((min_le_right ..).trans (min_le_left ..))⟩

def dyadicKernel (a b : ℝ) (ρ : ℂ) : ℝ → ℂ :=
  (Ioc a (b+1)).indicator (fun x => (dyadicTaper a b x:ℂ)*(x:ℂ)^(ρ-1))

def dyadicTransform (a b : ℝ) (ρ : ℂ) (v : ℝ) : ℂ :=
  ∫ x in a..b+1, (dyadicTaper a b x:ℂ)*phase (2*Real.pi*v*x)*(x:ℂ)^(ρ-1)

theorem dyadicTransform_fourier (a b : ℝ) (ρ : ℂ) (v : ℝ)
    (hab : a ≤ b+1) :
    dyadicTransform a b ρ v = 𝓕 (dyadicKernel a b ρ) (-v) := by
  rw [Real.fourier_real_eq_integral_exp_smul,dyadicTransform,intervalIntegral.integral_of_le hab]
  have he : (fun x => Complex.exp (↑(-2*Real.pi*x*(-v))*Complex.I) • dyadicKernel a b ρ x) =
    (Ioc a (b+1)).indicator (fun x => (dyadicTaper a b x:ℂ)*phase (2*Real.pi*v*x)*(x:ℂ)^(ρ-1)) := by
    funext x
    by_cases hx : x∈Ioc a (b+1)
    · rw [dyadicKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx]
      simp only [smul_eq_mul,phase]
      rw [show (-2*Real.pi*x*(-v))=2*Real.pi*v*x by ring]
      ring
    · simp [dyadicKernel,Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Ioc]

theorem dyadicTransform_energy (a b N : ℝ) (ρ : ℂ)
    (ha : 0<a) (hab : a≤b+1) (hN : b+1≤N) (hρ : 1/2<ρ.re) :
    Integrable (fun v => ‖dyadicTransform a b ρ v‖^2) ∧
      (∫ v, ‖dyadicTransform a b ρ v‖^2) ≤ N^(2*ρ.re-1)/(2*ρ.re-1) := by
  let f (x : ℝ) : ℂ := (dyadicTaper a b x:ℂ)*(x:ℂ)^(ρ-1)
  have hcont : ContinuousOn f (Icc a (b+1)) := by
    intro x hx
    have hx0 : 0<x := ha.trans_le hx.1
    have ht : Continuous (fun x : ℝ => dyadicTaper a b x) := by unfold dyadicTaper;fun_prop
    exact ((Complex.continuous_ofReal.comp ht).continuousAt.mul
      (differentiableAt_id.ofReal_cpow_const (ρ-1) hx0.ne').continuousAt).continuousWithinAt
  have hf : IntegrableOn f (Ioc a (b+1)) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfsq : IntegrableOn (fun x => ‖f x‖^2) (Ioc a (b+1)) :=
    (hcont.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hki : Integrable (dyadicKernel a b ρ) := by
    rw [dyadicKernel,integrable_indicator_iff measurableSet_Ioc]
    exact hf
  have hksq : (fun x => ‖dyadicKernel a b ρ x‖^2) =
      (Ioc a (b+1)).indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x∈Ioc a (b+1) <;> simp [dyadicKernel,f,hx]
  have hk₂ : MemLp (dyadicKernel a b ρ) 2 :=
    (memLp_two_iff_integrable_sq_norm hki.aestronglyMeasurable).mpr (by
      rw [hksq,integrable_indicator_iff measurableSet_Ioc];exact hfsq)
  obtain ⟨hi,he⟩ := box_plancherel hki hk₂
  have hpow (x : ℝ) (hx : x∈Ioc a (b+1)) :
      ‖f x‖^2 ≤ x^(2*ρ.re-2) := by
    have hx0 : 0<x := ha.trans hx.1
    have ht := dyadicTaper_bounds a b x
    dsimp [f]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0,Complex.sub_re,Complex.one_re]
    calc
      _ ≤ (x^(ρ.re-1))^2 :=
        pow_le_pow_left₀ (mul_nonneg ht.1 (Real.rpow_nonneg hx0.le _))
          (mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) ht.2) 2
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hx0.le]
        congr 1
        norm_num
        ring
  have hN0 : 0<N := ha.trans_le (hab.trans hN)
  have hp : IntegrableOn (fun x : ℝ => x^(2*ρ.re-2)) (Ioc 0 N) := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<2*ρ.re-2)).1
  have hsub : Ioc a (b+1) ⊆ Ioc 0 N :=
    fun x hx => ⟨ha.trans hx.1,hx.2.trans hN⟩
  have hfull : ∫ x, ‖dyadicKernel a b ρ x‖^2 ≤ N^(2*ρ.re-1)/(2*ρ.re-1) := by
    rw [hksq,integral_indicator measurableSet_Ioc]
    calc
      _ ≤ ∫ x in Ioc a (b+1), x^(2*ρ.re-2) :=
        setIntegral_mono_on hfsq (hp.mono_set hsub) measurableSet_Ioc hpow
      _ ≤ ∫ x in Ioc 0 N, x^(2*ρ.re-2) :=
        setIntegral_mono_set hp (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact Real.rpow_nonneg hx.1.le _) (Filter.Eventually.of_forall hsub)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hN0.le,
          integral_rpow (Or.inl (by linarith : -1<2*ρ.re-2)),
          show 2*ρ.re-2+1=2*ρ.re-1 by ring,Real.zero_rpow (by linarith : 2*ρ.re-1≠0),sub_zero]
  simp_rw [dyadicTransform_fourier a b ρ _ hab]
  constructor
  · simpa only [neg_one_mul] using hi.comp_mul_left' (by norm_num : (-1:ℝ)≠0)
  · calc
      _ = ∫ v, ‖𝓕 (dyadicKernel a b ρ) v‖^2 := by
        have h := Measure.integral_comp_mul_left (fun v => ‖𝓕 (dyadicKernel a b ρ) v‖^2) (-1:ℝ)
        simpa [neg_one_mul] using h
      _ ≤ _ := he.trans_le hfull


/-- The actual dyadic tapered pair with arbitrary windows.
This also permits the principal term rho=1. -/
def dyadicPair (a b c d : ℝ) (ρ σ : ℂ) (R n : ℝ) : ℂ :=
  ∫ v in -R..R, dyadicTransform a b ρ v * dyadicTransform c d σ v *
    phase (-(2*Real.pi*n*v))

theorem dyadicPair_uniform (a b c d N : ℝ) (ρ σ : ℂ) (R n : ℝ)
    (ha : 0<a) (hb : a≤b+1) (hc : 0<c) (hd : c≤d+1)
    (hbN : b+1≤N) (hdN : d+1≤N) (hN : 1≤N) (hR : 0≤R)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1)
    (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1) :
    ‖dyadicPair a b c d ρ σ R n‖ ≤ 2*N := by
  obtain ⟨hi₁,he₁⟩ := dyadicTransform_energy a b N ρ ha hb hbN (by linarith)
  obtain ⟨hi₂,he₂⟩ := dyadicTransform_energy c d N σ hc hd hdN (by linarith)
  have hscalar (t : ℝ) (h₁ : 3/4≤t) (h₂ : t≤1) :
      N^(2*t-1)/(2*t-1)≤2*N := by
    have ht : 0<2*t-1 := by linarith
    have hp : N^(2*t-1)≤N := by
      calc
        _ ≤ N^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        _ = _ := Real.rpow_one _
    apply (div_le_iff₀ ht).2
    have h := mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*t-1) by linarith) (by linarith : 0≤N)
    nlinarith only [hp,h]
  let f (v : ℝ) := (‖dyadicTransform a b ρ v‖^2+‖dyadicTransform c d σ v‖^2)/2
  have hf : Integrable f := (hi₁.add hi₂).div_const 2
  have hp (v : ℝ) :
      ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖≤f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    dsimp [f]
    nlinarith [sq_nonneg (‖dyadicTransform a b ρ v‖-‖dyadicTransform c d σ v‖)]
  have hA : ∀ v,0≤f v := by intro v;dsimp [f];positivity
  unfold dyadicPair
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R, ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R,f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hf.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v,f v := setIntegral_le_integral hf (Filter.Eventually.of_forall hA)
    _ ≤ 2*N := by
      dsimp [f]
      rw [integral_div,integral_add hi₁ hi₂]
      linarith only [he₁.trans (hscalar ρ.re hρ hρ1), he₂.trans (hscalar σ.re hσ hσ1)]


end
end InnerFloorZeroModel
end

namespace InnerFloorGaussPacket
open Finset RouteB_InnerFloorLinearTotient RouteB_InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
theorem boundedHighProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 0≤N) (J : ℕ→ℂ) (hJ : ∀ q∈S, ‖J q‖≤2*N) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * J q‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  dsimp only
  let c (q : ℕ) := productCoefficient q χ.conductor ψ.conductor D
  have hc (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ c q := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    have hq0 : 0 < q := (mem_Icc.mp hqR).1
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨hq0.ne'⟩
    have hp : D ≤ (DirichletCharacter.changeLevel hqL χ *
          DirichletCharacter.changeLevel hqL ψ).conductor := by
      rw [productConductor_changeLevel]
      exact hprod
    have h := signedCoefficient_highProduct
      (DirichletCharacter.changeLevel hqL χ) (DirichletCharacter.changeLevel hqL ψ) n D hn hD hp
    simpa only [c,DirichletCharacter.conductor_changeLevel] using h
  have hS' : S ⊆ (Icc 1 A).filter (fun q => χ.conductor∣q ∧ ψ.conductor∣q) := by
    intro q hq
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    exact mem_filter.mpr ⟨hqR,χ.conductor_dvd_level.trans hqL,ψ.conductor_dvd_level.trans hqL⟩
  have hsum : ∑ q∈S,c q ≤ weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
    apply (sum_le_sum_of_subset_of_nonneg hS' (fun q hq _ => ?_)).trans
      (productCoefficientFamily A χ.conductor ψ.conductor D
        (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos L))
        (Nat.pos_of_dvd_of_pos ψ.conductor_dvd_level (NeZero.pos L)) hD)
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq0
    have hlog := Real.log_nonneg hq1
    unfold productCoefficient
    positivity
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        J q‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S,c q*(2*N) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hc q hq) (hJ q hq)
        (norm_nonneg _) ((norm_nonneg _).trans (hc q hq))
    _ ≤ _ := by
      rw [← sum_mul]
      calc
        _ ≤ (weightConstant^3*(1+Real.log A)^4/Real.sqrt D)*(2*N) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = _ := by ring

/-- Exact taper-model version of the high-product packet estimate.
The radius and both dyadic windows may depend on the modulus. -/
theorem dyadicHighProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1) (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  apply boundedHighProduct_sum χ ψ A n D hn hD hprod S hS N (by linarith)
  intro q hq
  exact dyadicPair_uniform (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hρ1 hσ hσ1

end
end InnerFloorGaussPacket
#print axioms InnerFloorZeroModel.dyadicTransform_energy
#print axioms InnerFloorZeroModel.dyadicPair_uniform
#print axioms InnerFloorGaussPacket.boundedHighProduct_sum
#print axioms InnerFloorGaussPacket.dyadicHighProduct_sum

namespace InnerFloorGaussPacket
open Finset RouteB_InnerFloorLinearTotient RouteB_InnerFloorResearch InnerFloorZeroModel
open RouteB_DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem shiftedGauss_commonRatio {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n L : ℕ) (hn : 0 < n)
    (hL : 0 < L) (hLq : L∣q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))*(1+Real.log q) := by
  have hq : 0 < q := NeZero.pos q
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hlog : 0≤1+Real.log q := by linarith [Real.log_nonneg hq1]
  have hratio := gcdRatio_mono_multiple n L q hn hL hLq hq
  let r := (Nat.gcd n L:ℝ)/(L:ℝ)
  have hr : 0≤r := by dsimp [r]; positivity
  have hsq : (q:ℝ)*(Nat.gcd n q:ℝ) ≤ (q:ℝ)^2*r := by
    have h := (div_le_iff₀ hqR).mp hratio
    change (Nat.gcd n q:ℝ) ≤ r*(q:ℝ) at h
    calc
      _ ≤ (q:ℝ)*(r*(q:ℝ)) := mul_le_mul_of_nonneg_left h hqR.le
      _ = _ := by ring
  have hs : Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ)) ≤ (q:ℝ)*Real.sqrt r := by
    calc
      _ ≤ Real.sqrt ((q:ℝ)^2*r) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hqR.le]
  exact (shiftedGauss_geometricGcd χ n hn).trans (mul_le_mul_of_nonneg_right hs hlog)

/-- The common-level coefficient has a square-root saving when only a small
fraction of that level divides n. This applies to any product conductor. -/
theorem signedCoefficient_commonRatio {L q : ℕ} [NeZero L] [NeZero q]
    (hLq : L∣q) (χ ψ : DirichletCharacter ℂ L) (n A : ℕ)
    (hn : 0 < n) (hqA : q≤A) :
    ‖signedCoefficient (DirichletCharacter.changeLevel hLq χ)
      (DirichletCharacter.changeLevel hLq ψ) n‖ ≤
      weightConstant*(1+Real.log A)^2*
      Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))*((L:ℝ)/(q.totient:ℝ)) := by
  have hq : 0 < q := NeZero.pos q
  have hL : 0 < L := NeZero.pos L
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hlogq := Real.log_nonneg hq1
  have hlog : Real.log q≤Real.log A :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqA)
  have hlogA : 0≤Real.log A := hlogq.trans hlog
  have hratio : (q:ℝ)/(q.totient:ℝ)≤weightConstant*(1+Real.log A) :=
    (ratio_totient_le q hq).trans
      (mul_le_mul_of_nonneg_left (by linarith) weightConstant_nonneg)
  have hdχ : χ.conductor≤L := Nat.le_of_dvd hL χ.conductor_dvd_level
  have hdψ : ψ.conductor≤L := Nat.le_of_dvd hL ψ.conductor_dvd_level
  have hroot : Real.sqrt χ.conductor * Real.sqrt ψ.conductor ≤ (L:ℝ) := by
    calc
      _ ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hdχ))
          (Real.sqrt_le_sqrt (by exact_mod_cast hdψ))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  let r := Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))
  have hr : 0≤r := Real.sqrt_nonneg _
  let C := DirichletCharacter.changeLevel hLq χ
  let P := DirichletCharacter.changeLevel hLq ψ
  have hb := signedCoefficient_norm_le C P n
  dsimp [C,P] at hb
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel] at hb
  have hshift := shiftedGauss_commonRatio (C*P) n L hn hL hLq
  calc
    _ ≤ _ := hb
    _ ≤ (L:ℝ)*((q:ℝ)*r*(1+Real.log q))/(q.totient:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hroot hshift (norm_nonneg _) (Nat.cast_nonneg _)
    _ = ((L:ℝ)/(q.totient:ℝ))*((q:ℝ)/(q.totient:ℝ))*(1+Real.log q)*r := by ring
    _ ≤ ((L:ℝ)/(q.totient:ℝ))*(weightConstant*(1+Real.log A))*(1+Real.log A)*r := by
      apply mul_le_mul_of_nonneg_right _ hr
      apply mul_le_mul _ (by linarith) (by linarith)
        (mul_nonneg (by positivity) (mul_nonneg weightConstant_nonneg (by linarith)))
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

theorem boundedGcdRatio_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 0≤N) (J : ℕ→ℂ) (hJ : ∀ q∈S, ‖J q‖≤2*N) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * J q‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  dsimp only
  let K := weightConstant*(1+Real.log A)^2*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg weightConstant_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hcoef (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ K*((L:ℝ)/(q.totient:ℝ)) := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    obtain ⟨hq0,hqA⟩ := mem_Icc.mp hqR
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨(show 0 < q from hq0).ne'⟩
    exact signedCoefficient_commonRatio hqL χ ψ n A hn hqA
  have hsum : ∑ q∈S,(L:ℝ)/(q.totient:ℝ) ≤ (weightConstant*(1+Real.log A))^2 :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (commonMultipleTotientWeight A L (NeZero.pos L) hLA)
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        J q‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S, (K*((L:ℝ)/(q.totient:ℝ)))*(2*N) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hcoef q hq) (hJ q hq)
        (norm_nonneg _) ((norm_nonneg _).trans (hcoef q hq))
    _ = K*(∑ q∈S,(L:ℝ)/(q.totient:ℝ))*(2*N) := by rw [← sum_mul,← mul_sum]
    _ ≤ K*((weightConstant*(1+Real.log A))^2)*(2*N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hK) (by positivity)
    _ = _ := by dsimp [K];ring

theorem dyadicGcdRatio_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1) (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  apply boundedGcdRatio_sum χ ψ A n hn hLA S hS N (by linarith)
  intro q hq
  exact dyadicPair_uniform (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hρ1 hσ hσ1

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.shiftedGauss_commonRatio
#print axioms InnerFloorGaussPacket.signedCoefficient_commonRatio
#print axioms InnerFloorGaussPacket.boundedGcdRatio_sum
#print axioms InnerFloorGaussPacket.dyadicGcdRatio_sum

section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
set_option maxHeartbeats 2000000 in
/-- Preserve both zero real parts in the exact taper pair bound, rather than
discarding their combined power saving by replacing the energy by O(N). -/
theorem dyadicPair_realParts (a b c d N : ℝ) (ρ σ : ℂ) (R n : ℝ)
    (ha : 0<a) (hb : a≤b+1) (hc : 0<c) (hd : c≤d+1)
    (hbN : b+1≤N) (hdN : d+1≤N) (hN : 1≤N) (hR : 0≤R)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re) :
    ‖dyadicPair a b c d ρ σ R n‖ ≤ 2*N^(ρ.re+σ.re-1) := by
  obtain ⟨hi₁,he₁⟩ := dyadicTransform_energy a b N ρ ha hb hbN (by linarith)
  obtain ⟨hi₂,he₂⟩ := dyadicTransform_energy c d N σ hc hd hdN (by linarith)
  have hN0 : 0<N := by linarith
  let X := N^(ρ.re-1/2)
  let Y := N^(σ.re-1/2)
  have hX : 0<X := Real.rpow_pos_of_pos hN0 _
  have hY : 0<Y := Real.rpow_pos_of_pos hN0 _
  have hXeq : N^(2*ρ.re-1)=X^2 := by
    dsimp [X]
    rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    congr 1
    norm_num
    ring
  have hYeq : N^(2*σ.re-1)=Y^2 := by
    dsimp [Y]
    rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    congr 1
    norm_num
    ring
  have hE₁ : (∫ v, ‖dyadicTransform a b ρ v‖^2) ≤ 2*X^2 := by
    apply he₁.trans
    rw [hXeq]
    apply (div_le_iff₀ (by linarith : 0<2*ρ.re-1)).2
    nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*ρ.re-1) by linarith) (sq_nonneg X)]
  have hE₂ : (∫ v, ‖dyadicTransform c d σ v‖^2) ≤ 2*Y^2 := by
    apply he₂.trans
    rw [hYeq]
    apply (div_le_iff₀ (by linarith : 0<2*σ.re-1)).2
    nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*σ.re-1) by linarith) (sq_nonneg Y)]
  let f (v : ℝ) := (‖dyadicTransform a b ρ v‖^2/X^2+‖dyadicTransform c d σ v‖^2/Y^2)/2
  have hf : Integrable f := ((hi₁.div_const (X^2)).add (hi₂.div_const (Y^2))).div_const 2
  have hF₁ : (∫ v, ‖dyadicTransform a b ρ v‖^2/X^2) ≤ 2 := by
    rw [integral_div]
    exact (div_le_iff₀ (pow_pos hX 2)).2 hE₁
  have hF₂ : (∫ v, ‖dyadicTransform c d σ v‖^2/Y^2) ≤ 2 := by
    rw [integral_div]
    exact (div_le_iff₀ (pow_pos hY 2)).2 hE₂
  have hF : (∫ v,f v) ≤ 2 := by
    dsimp [f]
    rw [integral_div,integral_add (hi₁.div_const _) (hi₂.div_const _)]
    linarith
  have hp (v : ℝ) :
      ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖≤(X*Y)*f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    have h : ‖dyadicTransform a b ρ v‖*‖dyadicTransform c d σ v‖/(X*Y)≤f v := by
      dsimp [f]
      rw [show ‖dyadicTransform a b ρ v‖*‖dyadicTransform c d σ v‖/(X*Y)=
        (‖dyadicTransform a b ρ v‖/X)*(‖dyadicTransform c d σ v‖/Y) by
        field_simp]
      simp only [← div_pow]
      nlinarith [sq_nonneg (‖dyadicTransform a b ρ v‖/X-‖dyadicTransform c d σ v‖/Y)]
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hX hY)).1 h
  have hA : ∀ v,0≤(X*Y)*f v := by intro v;dsimp [f];positivity
  have hg : Integrable (fun v => (X*Y)*f v) := hf.const_mul _
  unfold dyadicPair
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R, ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R,(X*Y)*f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hg.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v,(X*Y)*f v := setIntegral_le_integral hg (Filter.Eventually.of_forall hA)
    _ ≤ 2*(X*Y) := by
      rw [integral_const_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hF (mul_pos hX hY).le
    _ = _ := by
      have hXY : X*Y=N^(ρ.re+σ.re-1) := by
        dsimp [X,Y]
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      rw [hXY]

end
end InnerFloorZeroModel
end
#print axioms InnerFloorZeroModel.dyadicPair_realParts

namespace InnerFloorGaussPacket
open Finset RouteB_InnerFloorLinearTotient RouteB_InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem dyadicHighProduct_realParts_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N^(ρ.re+σ.re-1)*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  apply boundedHighProduct_sum χ ψ A n D hn hD hprod S hS (N^(ρ.re+σ.re-1)) (Real.rpow_nonneg (by linarith) _)
  intro q hq
  exact dyadicPair_realParts (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hσ

theorem dyadicGcdRatio_realParts_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N^(ρ.re+σ.re-1)*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  apply boundedGcdRatio_sum χ ψ A n hn hLA S hS (N^(ρ.re+σ.re-1)) (Real.rpow_nonneg (by linarith) _)
  intro q hq
  exact dyadicPair_realParts (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hσ

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.dyadicHighProduct_realParts_sum
#print axioms InnerFloorGaussPacket.dyadicGcdRatio_realParts_sum


open scoped BigOperators
namespace RouteB_InnerFloorResearch
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
end RouteB_InnerFloorResearch
#print axioms RouteB_InnerFloorResearch.signedResidualPartition

open scoped BigOperators
namespace RouteB_InnerFloorResearch
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
end RouteB_InnerFloorResearch
#print axioms RouteB_InnerFloorResearch.sparseDeficitTerm
#print axioms RouteB_InnerFloorResearch.sparseDeficitSum

namespace RouteB_InnerFloorResearch
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
end RouteB_InnerFloorResearch
#print axioms RouteB_InnerFloorResearch.packetSavingBudget
#print axioms RouteB_InnerFloorResearch.quantitativeResidualPartition

namespace InnerFloorGaussPacket
open Finset RouteB_InnerFloorLinearTotient RouteB_InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

/-- Data for one primitive-zero pair, lifted to a common level. The windows
may vary with the rational denominator; the arc mask is kept as a subset. -/
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

/-- The same actual Gauss-normalized packet has all three bounds, with no
zero-free hypothesis, and no assertion about the prime spectral expansion. -/
theorem DyadicPacket.threeBounds (p : DyadicPacket) (A n : ℕ) (N : ℝ)
    (hn : 0<n) (hN : 1≤N) (hp : p.Admissible A N) :
    let B := (2*weightConstant^3)*(N^(p.ρ.re+p.σ.re-1)*(1+Real.log A)^(4:ℝ))
    ‖p.value n‖ ≤ B ∧ ‖p.value n‖ ≤ B*p.productSaving ∧
      ‖p.value n‖ ≤ B*p.gcdSaving n := by
  letI : NeZero p.level := ⟨p.level_pos.ne'⟩
  let D := (p.χ*p.ψ).conductor
  have hD : 0<D := Nat.pos_of_dvd_of_pos (p.χ*p.ψ).conductor_dvd_level p.level_pos
  have h0 := dyadicHighProduct_realParts_sum p.χ p.ψ A n 1 hn (by omega)
    (show 1≤D by omega) p.S hp.hS N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  have h1 := dyadicHighProduct_realParts_sum p.χ p.ψ A n D hn hD le_rfl p.S hp.hS
    N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  have h2 := dyadicGcdRatio_realParts_sum p.χ p.ψ A n hn hp.hLA p.S hp.hS
    N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  dsimp only at h0 h1 h2 ⊢
  rw [show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast]
  constructor
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h0).trans_eq
    norm_num
    ring
  constructor
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h1).trans_eq
    unfold DyadicPacket.productSaving
    dsimp [D]
    ring
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h2).trans_eq
    unfold DyadicPacket.gcdSaving
    ring

/-- Exact three-gate residual bound for any sparse collection of actual
Gauss-normalized tapered zero pairs. Only the residual intersection needs a
signed lower bound, provided the spectral expansion and sparsity are proved. -/
theorem actualPacketResidual {ι : Type*} (s : Finset ι) (p : ι→DyadicPacket)
    (A n : ℕ) (N r m : ℝ) (hA : 1≤A) (hn : 0<n) (hN : 1≤N)
    (hp : ∀ i∈s, (p i).Admissible A N)
    (hcard : (s.card:ℝ) ≤ (1+Real.log A)^r) :
    let L := 1+Real.log A
    (∑ i∈s.filter (fun i =>
      (2-(p i).ρ.re-(p i).σ.re)*Real.log N < (4+(m+r))*Real.log L ∧
      1 < L^(4+(m+r))*(p i).productSaving ∧
      1 < L^(4+(m+r))*(p i).gcdSaving n), ((p i).value n).re)
      -(2*weightConstant^3)*(N/L^m) ≤ ∑ i∈s, ((p i).value n).re := by
  dsimp only
  have hlog : 0 < 1+Real.log A := by
    linarith [Real.log_nonneg (show (1:ℝ)≤A by exact_mod_cast hA)]
  apply quantitativeResidualPartition s (fun i => (p i).value n)
    (fun i => (p i).ρ.re) (fun i => (p i).σ.re)
    (fun i => (p i).productSaving) (fun i => (p i).gcdSaving n)
    N (1+Real.log A) (2*weightConstant^3) 4 r m hN hlog
    (mul_nonneg (by norm_num) (pow_nonneg weightConstant_nonneg 3)) hcard
  · intro i hi; exact (hp i hi).hsum
  · intro i hi; unfold DyadicPacket.productSaving; positivity
  · intro i hi; unfold DyadicPacket.gcdSaving; positivity
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).1
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).2.1
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).2.2

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.DyadicPacket.threeBounds
#print axioms InnerFloorGaussPacket.actualPacketResidual


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
open Finset OAI.Ostmann InnerFloorGaussPacket RouteB_InnerFloorLinearTotient
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
  apply RouteB_InnerFloorResearch.quantitativeResidualPartition s (fun ij => (p ij).value n)
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
open Finset OAI.Ostmann InnerFloorGaussPacket RouteB_InnerFloorLinearTotient
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


/-!
Route B Research Thresholds & Escape-Hatch Formalization:
1. Even Real Diagonal Positivity: for an even primitive quadratic character
   (`χ (-1) = 1`) and any nonnegative real kernel `w ≥ 0`, both the Gauss-sum
   square `+(q : ℂ)` and the self-convolution `∑ k ≤ n, w k * w (n - k)` are
   nonnegative, so even Siegel zeros contribute positively to the signed floor.
2. Exact Necessity & Sufficiency Threshold for Odd Real Zeros:
   - Necessity (`oddReal_logGap_violates_floor`): at `n = q^k` with `β = 1 - c/log q`,
     `-(q/φ(q)) * n^(2β - 1) ≤ -exp(-2kc) * n`, violating `-εn` for `ε < exp(-2kc)`.
   - Sufficiency (`oddReal_superLogGap_satisfies_floor`): whenever
     `(1 - β) * log n ≥ (1/2) * log (q / (φ(q) * ε))`, we have
     `-(ε * n) ≤ -(q/φ(q)) * n^(2β - 1)`.
3. Almost-All Escape Hatch (`multiples_card_le_div`): the set of `n ∈ Icc 1 X`
   divisible by `d ≥ 1` has cardinality at most `X / d`, explaining formally why
   Gate 3 (`gcdSaving`) eliminates an odd exceptional conductor for almost all
   even `n ≤ X`, whereas the pointwise `∀ n ≥ N, Even n` frozen statement
   cannot avoid `d ∣ n`.
-/
namespace InnerFloorRouteBThreshold
open Finset AddChar MulChar
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Nonnegativity of discrete self-convolution for any nonnegative real kernel. -/
theorem selfConvolution_nonneg (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), w k * w (n - k) :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (hw (n - k))

/-- For an even real diagonal term (positive Gauss-sum factor `q / φ(q)` and
    nonnegative self-convolution), the signed contribution is nonnegative. -/
theorem evenRealDiag_contribution_nonneg (q n : ℕ)
    (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ ((q : ℝ) / (q.totient : ℝ)) * (∑ k ∈ Finset.range (n + 1), w k * w (n - k)) := by
  have hφ : 0 ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg q) hφ) (selfConvolution_nonneg w hw n)

/-- Exact identity `n^(2β - 1) = n * exp(-2 * (1 - β) * log n)` for `n > 0`. -/
theorem rpow_two_beta_sub_one_eq (n β : ℝ) (hn : 0 < n) :
    n ^ (2 * β - 1) = n * Real.exp (-(2 * (1 - β) * Real.log n)) := by
  rw [Real.rpow_def_of_pos hn]
  have h1 : Real.log n * (2 * β - 1) = Real.log n + -(2 * (1 - β) * Real.log n) := by ring
  rw [h1, Real.exp_add, Real.exp_log hn]

/-- Necessity: if `n = q^k` (`q > 1`, `k > 0`) and `β = 1 - c / log q`, then
    the odd real diagonal contribution `-(q/φ(q)) * n^(2β - 1)` is bounded
    above by `-exp(-2kc) * n`, violating `-εn` whenever `ε < exp(-2kc)`. -/
theorem oddReal_logGap_violates_floor (q : ℕ) (hq : 1 < q) (k c ε : ℝ)
    (hε : ε < Real.exp (-(2 * k * c))) :
    let n : ℝ := (q : ℝ) ^ k;
    let β : ℝ := 1 - c / Real.log (q : ℝ);
    -((q : ℝ) / (q.totient : ℝ)) * n ^ (2 * β - 1) < -(ε * n) := by
  dsimp only
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hnp : 0 < (q : ℝ) ^ k := Real.rpow_pos_of_pos hqp k
  have hlogq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hqR).ne'
  rw [rpow_two_beta_sub_one_eq ((q : ℝ) ^ k) (1 - c / Real.log (q : ℝ)) hnp]
  rw [Real.log_rpow hqp]
  have hexp : -(2 * (1 - (1 - c / Real.log (q : ℝ))) * (k * Real.log (q : ℝ))) = -(2 * k * c) := by
    field_simp
    ring
  rw [hexp]
  have hφp : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hratio : 1 ≤ (q : ℝ) / (q.totient : ℝ) :=
    (le_div_iff₀ hφp).2 (by simpa only [one_mul] using
      (show (q.totient : ℝ) ≤ (q : ℝ) by exact_mod_cast Nat.totient_le q))
  have hepos : 0 < Real.exp (-(2 * k * c)) := Real.exp_pos _
  have h1 : Real.exp (-(2 * k * c)) * (q : ℝ) ^ k ≤
      ((q : ℝ) / (q.totient : ℝ)) * ((q : ℝ) ^ k * Real.exp (-(2 * k * c))) := by
    have hm := mul_le_mul_of_nonneg_right hratio (mul_pos hnp hepos).le
    nlinarith only [hm]
  have h2 : ε * (q : ℝ) ^ k < Real.exp (-(2 * k * c)) * (q : ℝ) ^ k :=
    mul_lt_mul_of_pos_right hε hnp
  linarith only [h1, h2]

/-- Sufficiency: if `(1 - β) * log n ≥ (1/2) * log (q / (φ(q) * ε))` for `n > 0`,
    `q ≥ 1`, `ε > 0`, then the odd real diagonal contribution is absorbed into
    the one-sided floor `-(ε * n)`. -/
theorem oddReal_superLogGap_satisfies_floor (q : ℕ) (hq : 0 < q)
    (n β ε : ℝ) (hn : 0 < n) (hε : 0 < ε)
    (hgap : (1 / 2 : ℝ) * Real.log ((q : ℝ) / ((q.totient : ℝ) * ε)) ≤ (1 - β) * Real.log n) :
    -(ε * n) ≤ -((q : ℝ) / (q.totient : ℝ)) * n ^ (2 * β - 1) := by
  rw [rpow_two_beta_sub_one_eq n β hn]
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hφp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have harg : 0 < (q : ℝ) / ((q.totient : ℝ) * ε) := by positivity
  have h2 : Real.log ((q : ℝ) / ((q.totient : ℝ) * ε)) ≤ 2 * (1 - β) * Real.log n := by
    linarith only [hgap]
  have hexp : (q : ℝ) / ((q.totient : ℝ) * ε) ≤ Real.exp (2 * (1 - β) * Real.log n) := by
    rw [← Real.exp_log harg]
    exact Real.exp_le_exp.mpr h2
  have hinv : Real.exp (-(2 * (1 - β) * Real.log n)) ≤ (q.totient : ℝ) * ε / (q : ℝ) := by
    rw [Real.exp_neg]
    have hpos : 0 < Real.exp (2 * (1 - β) * Real.log n) := Real.exp_pos _
    rw [inv_le_iff_one_le_mul₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left hexp (div_nonneg (mul_nonneg hφp.le hε.le) hqp.le)
    have hcancel : (q.totient : ℝ) * ε / (q : ℝ) * ((q : ℝ) / ((q.totient : ℝ) * ε)) = 1 := by
      field_simp
    linarith only [hmul, hcancel]
  have hcoeff : ((q : ℝ) / (q.totient : ℝ)) * Real.exp (-(2 * (1 - β) * Real.log n)) ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left hinv (div_nonneg hqp.le hφp.le)
    have hsimp : (q : ℝ) / (q.totient : ℝ) * ((q.totient : ℝ) * ε / (q : ℝ)) = ε := by
      field_simp
    linarith only [hm, hsimp]
  have hn_mul := mul_le_mul_of_nonneg_right hcoeff hn.le
  linarith only [hn_mul]

/-- Almost-all escape hatch: the number of integers `n ∈ Icc 1 X` divisible by
    `d ≥ 1` is at most `X / d`. -/
theorem multiples_card_le_div (X d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card ≤ X / d := by
  have hinj : ∀ a ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
      ∀ b ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n), a / d = b / d → a = b := by
    intro a ha b hb hab
    have hda : d ∣ a := (Finset.mem_filter.mp ha).2
    have hdb : d ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = d * (a / d) := (Nat.mul_div_cancel' hda).symm
      _ = d * (b / d) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hdb
  have hmaps : ∀ a ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
      a / d ∈ Finset.Icc 1 (X / d) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hrange := Finset.mem_Icc.mp ha'.1
    have hda : d ∣ a := ha'.2
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hrange.2⟩
    rcases hda with ⟨k, rfl⟩
    have hk : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      omega
    rw [Nat.mul_div_right k hd]
    exact hk
  calc
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card
        ≤ (Finset.Icc 1 (X / d)).card := Finset.card_le_card_of_injOn (fun a => a / d) hmaps hinj
    _ = X / d := by simp

end
end InnerFloorRouteBThreshold

#print axioms InnerFloorRouteBThreshold.selfConvolution_nonneg
#print axioms InnerFloorRouteBThreshold.evenRealDiag_contribution_nonneg
#print axioms InnerFloorRouteBThreshold.oddReal_logGap_violates_floor
#print axioms InnerFloorRouteBThreshold.oddReal_superLogGap_satisfies_floor
#print axioms InnerFloorRouteBThreshold.multiples_card_le_div


/-!
Route B Unconditional Almost-All Even n Closure (Gate-3 Exceptional Set Density):
Proves that for any finite family of exceptional conductors `D` and any
Gate-3 threshold `M > 0`, the set of integers `n ∈ Icc 1 X` whose gcd ratio
`gcd(n, d) / d` exceeds `1 / M` for some `d ∈ D` has cardinality bounded by
`∑ d ∈ D, ∑ g ∈ d.divisors with d < g * M, (X / g)`, and in real-valued form by
`(X : ℝ) * M * ∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)`.

Consequently, even without ruling out hypothetical odd Siegel zeros or q-aspect
log-gap zeros, Gate 3 (`gcdSaving`) eliminates the entire triple-gate residual
for all `n ≤ X` outside an explicit exceptional set of density
`O(M * ∑_{d ∈ D} τ(d) / d)`.
-/
namespace InnerFloorRouteBAlmostAll
open Finset
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Number of integers `n ∈ Icc 1 X` divisible by `g > 0` is at most `X / g`. -/
theorem multiples_card_le_div (X g : ℕ) (hg : 0 < g) :
    ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card ≤ X / g := by
  have hinj : ∀ a ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n),
      ∀ b ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n), a / g = b / g → a = b := by
    intro a ha b hb hab
    have hga : g ∣ a := (Finset.mem_filter.mp ha).2
    have hgb : g ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = g * (a / g) := (Nat.mul_div_cancel' hga).symm
      _ = g * (b / g) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hgb
  have hmaps : ∀ a ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n),
      a / g ∈ Finset.Icc 1 (X / g) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hrange := Finset.mem_Icc.mp ha'.1
    have hga : g ∣ a := ha'.2
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hrange.2⟩
    rcases hga with ⟨k, rfl⟩
    have hk : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      omega
    rw [Nat.mul_div_right k hg]
    exact hk
  calc
    ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card
        ≤ (Finset.Icc 1 (X / g)).card := Finset.card_le_card_of_injOn (fun a => a / g) hmaps hinj
    _ = X / g := by simp

/-- High-gcd exceptional set for a single conductor `d` and real threshold `M`:
    all `n ∈ Icc 1 X` such that `(d : ℝ) < (Nat.gcd n d : ℝ) * M`. -/
def highGcdSet (X d : ℕ) (M : ℝ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => (d : ℝ) < (Nat.gcd n d : ℝ) * M)

/-- Every `n ∈ highGcdSet X d M` is divisible by some divisor `g ∣ d`
    satisfying `(d : ℝ) < (g : ℝ) * M`. -/
theorem highGcdSet_subset_biUnion (X d : ℕ) (hd : 0 < d) (M : ℝ) :
    highGcdSet X d M ⊆
      (d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).biUnion
        (fun g => (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)) := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  refine Finset.mem_biUnion.mpr ⟨Nat.gcd n d, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n d, hd.ne'⟩, hn'.2⟩
  · exact Finset.mem_filter.mpr ⟨hn'.1, Nat.gcd_dvd_left n d⟩

/-- Exact combinatorial bound for a single conductor `d`:
    `|highGcdSet X d M| ≤ ∑_{g ∣ d, d < g * M} (X / g)`. -/
theorem highGcdSet_card_le_sum_div (X d : ℕ) (hd : 0 < d) (M : ℝ) :
    (highGcdSet X d M).card ≤
      ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g := by
  calc
    (highGcdSet X d M).card
        ≤ ((d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).biUnion
            (fun g => (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n))).card :=
          Finset.card_le_card (highGcdSet_subset_biUnion X d hd M)
    _ ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M),
          ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g := by
          apply Finset.sum_le_sum
          intro g hg
          have hgd : g ∣ d := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
          have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgd hd
          exact multiples_card_le_div X g hgpos

/-- Real-valued density bound for a single conductor `d > 0` and `M ≥ 0`:
    `|highGcdSet X d M| ≤ X * M * τ(d) / d`. -/
theorem highGcdSet_card_le_real (X d : ℕ) (hd : 0 < d) (M : ℝ) (hM : 0 ≤ M) :
    ((highGcdSet X d M).card : ℝ) ≤ (X : ℝ) * M * (d.divisors.card : ℝ) / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((highGcdSet X d M).card : ℝ) ≤
      ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X / g : ℕ) : ℝ) := by
    simpa only [Nat.cast_sum] using (show ((highGcdSet X d M).card : ℝ) ≤ ((∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g : ℕ) : ℝ) by exact_mod_cast highGcdSet_card_le_sum_div X d hd M)
  have hterm : ∀ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M),
      ((X / g : ℕ) : ℝ) ≤ (X : ℝ) * M / (d : ℝ) := by
    intro g hg
    have hgd : g ∣ d := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
    have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgd hd
    have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
    have hlt : (d : ℝ) < (g : ℝ) * M := (Finset.mem_filter.mp hg).2
    have hdiv : ((X / g : ℕ) : ℝ) ≤ (X : ℝ) / (g : ℝ) := by
      rw [le_div_iff₀ hgR]
      exact_mod_cast Nat.div_mul_le_self X g
    have hinv : (X : ℝ) / (g : ℝ) ≤ (X : ℝ) * M / (d : ℝ) := by
      rw [div_le_div_iff₀ hgR hdR]
      have hmul := mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg (α := ℝ) X)
      linarith only [hmul]
    exact hdiv.trans hinv
  calc
    ((highGcdSet X d M).card : ℝ)
        ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X / g : ℕ) : ℝ) := h1
    _ ≤ ∑ _g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X : ℝ) * M / (d : ℝ)) :=
          Finset.sum_le_sum hterm
    _ = ((d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).card : ℝ) * ((X : ℝ) * M / (d : ℝ)) := by
          simp
    _ ≤ (d.divisors.card : ℝ) * ((X : ℝ) * M / (d : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_filter_le d.divisors _
          · positivity
    _ = (X : ℝ) * M * (d.divisors.card : ℝ) / (d : ℝ) := by ring

/-- Family-wide almost-all exceptional set bound:
    for any finite family `D` of positive conductors and threshold `M ≥ 0`,
    the number of integers `n ∈ Icc 1 X` that fail Gate 3 for at least one `d ∈ D`
    is at most `X * M * ∑_{d ∈ D} τ(d) / d`. -/
theorem familyHighGcd_card_le_real (X : ℕ) (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    (M : ℝ) (hM : 0 ≤ M) :
    (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤
      (X : ℝ) * M * (∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)) := by
  have hsub :
      (Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M) ⊆
        D.biUnion (fun d => highGcdSet X d M) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    rcases hn'.2 with ⟨d, hd, hlt⟩
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hn'.1, hlt⟩⟩
  have hcard :
      (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤
        ∑ d ∈ D, ((highGcdSet X d M).card : ℝ) := by
    have hnat :
        ((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card ≤
          ∑ d ∈ D, (highGcdSet X d M).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    simpa only [Nat.cast_sum] using (show (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤ ((∑ d ∈ D, (highGcdSet X d M).card : ℕ) : ℝ) by exact_mod_cast hnat)
  calc
    (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ)
        ≤ ∑ d ∈ D, ((highGcdSet X d M).card : ℝ) := hcard
    _ ≤ ∑ d ∈ D, ((X : ℝ) * M * ((d.divisors.card : ℝ) / (d : ℝ))) := by
          apply Finset.sum_le_sum
          intro d hd
          simpa only [mul_div_assoc] using highGcdSet_card_le_real X d (hD d hd) M hM
    _ = (X : ℝ) * M * (∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)) := by
          rw [Finset.mul_sum]

end
end InnerFloorRouteBAlmostAll

#print axioms InnerFloorRouteBAlmostAll.multiples_card_le_div
#print axioms InnerFloorRouteBAlmostAll.highGcdSet_card_le_sum_div
#print axioms InnerFloorRouteBAlmostAll.highGcdSet_card_le_real
#print axioms InnerFloorRouteBAlmostAll.familyHighGcd_card_le_real


/-!
Route B Four-Gate Residual & Joint Gauss--Ramanujan Sign Obstruction:
1. `fourGateResidualPartition`: extends the 3-gate quantitative residual partition
   to FOUR independent attenuation gates:
   - Gate 1: real-part deficit `(2 - β₁ - β₂) * log N ≥ (4 + m + r) * log L`
   - Gate 2: product conductor saving `L^(4 + m + r) * prodSav ≤ 1`
   - Gate 3: gcd ratio saving `L^(4 + m + r) * gcdSav ≤ 1`
   - Gate 4 (NEW): imaginary height saving `L^(4 + m + r) * heightSav ≤ 1`
2. `jointSign_even_countermodel_neg`: exact arithmetic coefficient bound
   `3p * (-(p-1)) / (2*(p-1))^2 = -3p / (4*(p-1)) ≤ -3/4` for the even
   conductor `d = 3p` (`p ≡ 3 (mod 4)`, `n = 2p^8`) countermodel.
3. `global_mod3_forced_one` & `global_parity_annihilation_mod_3p`: proves that
   for ANY prime `p ≠ 3` and ANY `p₁ + p₂ = 2p^8` with `3 ∤ p₁`, `3 ∤ p₂`,
   we necessarily have `p₁ ≡ 1 (mod 3)`, `p₂ ≡ 1 (mod 3)`, and `p₁ ≡ -p₂ (mod p)` —
   so an even composite Siegel character `χ = χ₃ * χ_p` (`χ₃` odd, `χ_p` odd)
   forces `χ(p₁) = -χ(p₂)` globally, annihilating Goldbach representations
   just like an odd character at `d ∣ n`.
-/
namespace InnerFloorRouteBFourGate
open Finset
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Four-gate quantitative residual partition: any index in `s` that clears
    at least one of the 4 gates (real-part, product conductor, gcd ratio, or
    imaginary height) contributes at most `C * N / L^(m + r)`, so with
    `|s| ≤ L^r` all cleared terms sum to at most `C * N / L^m`. -/
theorem fourGateResidualPartition {ι : Type*} (s : Finset ι)
    (val : ι → ℂ) (β₁ β₂ prodSav gcdSav heightSav : ι → ℝ)
    (N L C k r m : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ L ^ r)
    (_hβ : ∀ i ∈ s, β₁ i + β₂ i ≤ 2)
    (_hprod0 : ∀ i ∈ s, 0 ≤ prodSav i)
    (_hgcd0 : ∀ i ∈ s, 0 ≤ gcdSav i)
    (_hht0 : ∀ i ∈ s, 0 ≤ heightSav i)
    (hb_re : ∀ i ∈ s, ‖val i‖ ≤ C * N ^ (β₁ i + β₂ i - 1) * L ^ k)
    (hb_prod : ∀ i ∈ s, ‖val i‖ ≤ C * N * L ^ k * prodSav i)
    (hb_gcd : ∀ i ∈ s, ‖val i‖ ≤ C * N * L ^ k * gcdSav i)
    (hb_ht : ∀ i ∈ s, ‖val i‖ ≤ C * N * L ^ k * heightSav i) :
    let R4 := s.filter (fun i =>
      (2 - β₁ i - β₂ i) * Real.log N < (k + (m + r)) * Real.log L ∧
      1 < L ^ (k + (m + r)) * prodSav i ∧
      1 < L ^ (k + (m + r)) * gcdSav i ∧
      1 < L ^ (k + (m + r)) * heightSav i)
    (∑ i ∈ R4, (val i).re) - C * (N / L ^ m) ≤ ∑ i ∈ s, (val i).re := by
  dsimp only
  set P : ι → Prop := fun i =>
    (2 - β₁ i - β₂ i) * Real.log N < (k + (m + r)) * Real.log L ∧
    1 < L ^ (k + (m + r)) * prodSav i ∧
    1 < L ^ (k + (m + r)) * gcdSav i ∧
    1 < L ^ (k + (m + r)) * heightSav i
  have hNp : 0 < N := by linarith
  have hLpos : 0 < L ^ (m + r) := Real.rpow_pos_of_pos hL _
  have hsplit : (∑ i ∈ s, (val i).re) =
      (∑ i ∈ s.filter P, (val i).re) + (∑ i ∈ s.filter (fun i => ¬P i), (val i).re) :=
    (Finset.sum_filter_add_sum_filter_not s P (fun i => (val i).re)).symm
  rw [hsplit]
  suffices htail : -(∑ i ∈ s.filter (fun i => ¬P i), (val i).re) ≤ C * (N / L ^ m) by
    linarith
  have hterm : ∀ i ∈ s.filter (fun i => ¬P i),
      -(val i).re ≤ C * N / L ^ (m + r) := by
    intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hnot : ¬P i := (Finset.mem_filter.mp hi).2
    have hre : -(val i).re ≤ ‖val i‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    have hnorm : ‖val i‖ ≤ C * N / L ^ (m + r) := by
      have hLk : L ^ k / L ^ (k + (m + r)) = 1 / L ^ (m + r) := by
        rw [Real.rpow_add hL]
        field_simp
      by_cases h1 : (k + (m + r)) * Real.log L ≤ (2 - β₁ i - β₂ i) * Real.log N
      · have hexp : N ^ (β₁ i + β₂ i - 1) ≤ N / L ^ (k + (m + r)) := by
          have h1' : Real.log (L ^ (k + (m + r))) ≤ Real.log (N ^ (2 - β₁ i - β₂ i)) := by
            rw [Real.log_rpow hL, Real.log_rpow hNp]
            exact h1
          have h2 : L ^ (k + (m + r)) ≤ N ^ (2 - β₁ i - β₂ i) := by
            rw [← Real.exp_log (Real.rpow_pos_of_pos hL _),
                ← Real.exp_log (Real.rpow_pos_of_pos hNp _)]
            exact Real.exp_le_exp.mpr h1'
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hL _)]
          calc
            N ^ (β₁ i + β₂ i - 1) * L ^ (k + (m + r))
                ≤ N ^ (β₁ i + β₂ i - 1) * N ^ (2 - β₁ i - β₂ i) :=
                  mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hNp.le _)
            _ = N ^ ((β₁ i + β₂ i - 1) + (2 - β₁ i - β₂ i)) := (Real.rpow_add hNp _ _).symm
            _ = N := by
                  have ha : (β₁ i + β₂ i - 1) + (2 - β₁ i - β₂ i) = 1 := by ring
                  rw [ha, Real.rpow_one]
        calc
          ‖val i‖ ≤ C * N ^ (β₁ i + β₂ i - 1) * L ^ k := hb_re i his
          _ ≤ C * (N / L ^ (k + (m + r))) * L ^ k := by
                have hm := mul_le_mul_of_nonneg_left hexp hC
                exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hL.le _)
          _ = C * N * (L ^ k / L ^ (k + (m + r))) := by ring
          _ = C * N / L ^ (m + r) := by rw [hLk]; ring
      · by_cases h2 : L ^ (k + (m + r)) * prodSav i ≤ 1
        · have hsav : prodSav i ≤ 1 / L ^ (k + (m + r)) :=
            (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).2 (by linarith)
          calc
            ‖val i‖ ≤ C * N * L ^ k * prodSav i := hb_prod i his
            _ ≤ C * N * L ^ k * (1 / L ^ (k + (m + r))) :=
                  mul_le_mul_of_nonneg_left hsav (by positivity)
            _ = C * N * (L ^ k / L ^ (k + (m + r))) := by ring
            _ = C * N / L ^ (m + r) := by rw [hLk]; ring
        · by_cases h3 : L ^ (k + (m + r)) * gcdSav i ≤ 1
          · have hsav : gcdSav i ≤ 1 / L ^ (k + (m + r)) :=
              (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).2 (by linarith)
            calc
              ‖val i‖ ≤ C * N * L ^ k * gcdSav i := hb_gcd i his
              _ ≤ C * N * L ^ k * (1 / L ^ (k + (m + r))) :=
                    mul_le_mul_of_nonneg_left hsav (by positivity)
              _ = C * N * (L ^ k / L ^ (k + (m + r))) := by ring
              _ = C * N / L ^ (m + r) := by rw [hLk]; ring
          · have h4 : L ^ (k + (m + r)) * heightSav i ≤ 1 := by
              by_contra hc
              exact hnot ⟨lt_of_not_ge h1, lt_of_not_ge h2, lt_of_not_ge h3, lt_of_not_ge hc⟩
            have hsav : heightSav i ≤ 1 / L ^ (k + (m + r)) :=
              (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).2 (by linarith)
            calc
              ‖val i‖ ≤ C * N * L ^ k * heightSav i := hb_ht i his
              _ ≤ C * N * L ^ k * (1 / L ^ (k + (m + r))) :=
                    mul_le_mul_of_nonneg_left hsav (by positivity)
              _ = C * N * (L ^ k / L ^ (k + (m + r))) := by ring
              _ = C * N / L ^ (m + r) := by rw [hLk]; ring
    exact hre.trans hnorm
  rw [← Finset.sum_neg_distrib]
  calc
    ∑ i ∈ s.filter (fun i => ¬P i), -(val i).re
        ≤ ∑ _i ∈ s.filter (fun i => ¬P i), (C * N / L ^ (m + r)) := Finset.sum_le_sum hterm
    _ = ((s.filter (fun i => ¬P i)).card : ℝ) * (C * N / L ^ (m + r)) := by simp
    _ ≤ (s.card : ℝ) * (C * N / L ^ (m + r)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_filter_le s _
          · positivity
    _ ≤ L ^ r * (C * N / L ^ (m + r)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C * (N / L ^ m) := by
          rw [Real.rpow_add hL]
          field_simp

/-- Exact negative arithmetic factor for GPT's even countermodel `d = 3p`,
    `p > 3`, `n = 2p^8`: `(3p) * (-(p-1)) / (2(p-1))^2 = -3p / (4(p-1)) ≤ -3/4`. -/
theorem jointSign_even_countermodel_neg (p : ℕ) (hp : 3 < p) :
    ((3 * p : ℝ) * (-(p - 1 : ℝ))) / ((2 * (p - 1 : ℝ)) ^ 2) ≤ -(3 / 4 : ℝ) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (3 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hEq : ((3 * p : ℝ) * (-(p - 1 : ℝ))) / ((2 * (p - 1 : ℝ)) ^ 2) =
      -(3 * (p : ℝ)) / (4 * ((p : ℝ) - 1)) := by
    field_simp
    ring
  rw [hEq, div_le_iff₀ (by positivity : 0 < 4 * ((p : ℝ) - 1))]
  linarith

/-- Global parity annihilation for `n = 2p^8` (`3 ∤ p`): any two naturals
    `p₁, p₂` coprime to `3` with `p₁ + p₂ = 2p^8` MUST both satisfy `≡ 1 (mod 3)`
    and `p₁ ≡ -p₂ (mod p)`.  Hence `χ₃(p₁) = χ₃(p₂) = 1` while `χ_p(p₁) = -χ_p(p₂)`
    for odd `χ_p`, forcing `χ(p₁) = -χ(p₂)` even though `χ = χ₃ * χ_p` is EVEN! -/
theorem global_mod3_forced_one (p p₁ p₂ : ℕ) (hp3 : ¬(3 ∣ p))
    (h1 : ¬(3 ∣ p₁)) (h2 : ¬(3 ∣ p₂)) (hsum : p₁ + p₂ = 2 * p ^ 8) :
    p₁ % 3 = 1 ∧ p₂ % 3 = 1 := by
  have hmodp : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hp8 : (p ^ 8) % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmodp with h | h <;> simp [h]
  have h2p8 : (2 * p ^ 8) % 3 = 2 := by
    rw [Nat.mul_mod, hp8]
  have hsum3 : (p₁ + p₂) % 3 = 2 := by rw [hsum, h2p8]
  omega

theorem global_modp_neg (p p₁ p₂ : ℕ) (hsum : p₁ + p₂ = 2 * p ^ 8) :
    ((p₁ : ZMod p) = -((p₂ : ZMod p))) := by
  have hcast : ((p₁ + p₂ : ℕ) : ZMod p) = ((2 * p ^ 8 : ℕ) : ZMod p) :=
    congrArg (Nat.cast : ℕ → ZMod p) hsum
  have hzero : ((2 * p ^ 8 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨2 * p ^ 7, by ring⟩
  rw [Nat.cast_add, hzero] at hcast
  exact eq_neg_of_add_eq_zero_left hcast

end
end InnerFloorRouteBFourGate

#print axioms InnerFloorRouteBFourGate.fourGateResidualPartition
#print axioms InnerFloorRouteBFourGate.jointSign_even_countermodel_neg
#print axioms InnerFloorRouteBFourGate.global_mod3_forced_one
#print axioms InnerFloorRouteBFourGate.global_modp_neg


end

section
namespace InnerFloorIndependentEulerMass
open Finset
noncomputable section

/-- A telescoping majorant for the reciprocal squares of the predecessor
of every odd integer greater than one. -/
theorem oddIndexMass (M : ℕ) :
    (∑ j ∈ range M, 1/(4*((j:ℝ)+1)^2)) ≤ (1/2:ℝ) := by
  have htel : (∑ j ∈ range M, 1/((2*(j:ℝ)+1)*(2*(j:ℝ)+3))) =
      (1/2:ℝ)*(1-1/(2*(M:ℝ)+1)) := by
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [sum_range_succ,ih,Nat.cast_succ]
      have h : (0:ℝ)≤(M:ℝ) := Nat.cast_nonneg M
      field_simp; ring
  calc
    _ ≤ ∑ j ∈ range M, 1/((2*(j:ℝ)+1)*(2*(j:ℝ)+3)) := by
      apply sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = _ := htel
    _ ≤ _ := by
      have h : (0:ℝ)≤1/(2*(M:ℝ)+1) := by positivity
      linarith

/-- The absolute tail over all nonempty subsets of a finite prime-index
family is below 2/3 when the total local mass is at most 1/2. -/
theorem subsetTailMass {ι : Type*} [DecidableEq ι] (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0≤a i) (hS : ∑ i ∈ P,a i ≤ (1/2:ℝ)) :
    (∑ t ∈ P.powerset.erase ∅, ∏ i ∈ t,a i) ≤ (2/3:ℝ) := by
  have hp : (∏ i ∈ P, (1+a i)) ≤ Real.exp (∑ i ∈ P,a i) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun i hi => by linarith [ha i hi])
      (fun i hi => by simpa [add_comm] using Real.add_one_le_exp (a i))
  have hE : Real.exp (1/2:ℝ) < 5/3 := by
    have h2 : Real.exp (1/2:ℝ)^2 = Real.exp 1 := by
      rw [pow_two,←Real.exp_add]
      norm_num
    have h3 : Real.exp 1 < (25/9:ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    by_contra! h
    nlinarith only [h2,h3,mul_le_mul h h (by norm_num : (0:ℝ)≤5/3) (Real.exp_nonneg _)]
  have hwhole : (∑ t ∈ P.powerset, ∏ i ∈ t,a i) < (5/3:ℝ) := by
    rw [← prod_one_add]
    exact hp.trans_lt ((Real.exp_le_exp.mpr hS).trans_lt hE)
  have he : (∅ : Finset ι) ∈ P.powerset := by simp
  have hs := sum_erase_add P.powerset (fun t => ∏ i ∈ t,a i) he
  simp only [prod_empty] at hs
  linarith only [hs,hwhole]

/-- The actual finite family of odd squarefree cofactors m>1 has a
uniform absolute reciprocal totient-square tail at most 2/3. -/
theorem oddSquarefreeTotientTail (M : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, 1 < m ∧ m ≤ M ∧ Odd m ∧ Squarefree m) :
    (∑ m ∈ S, 1/((m.totient:ℝ)^2)) ≤ (2/3:ℝ) := by
  let P := (range M).image (fun j : ℕ => 2*j+3)
  let a := fun p : ℕ => 1/((p:ℝ)-1)^2
  have hP : ∑ p ∈ P,a p ≤ (1/2:ℝ) := by
    unfold P
    rw [sum_image (by intro i hi j hj h; change 2*i+3=2*j+3 at h; omega)]
    calc
      _ = ∑ j ∈ range M,1/(4*((j:ℝ)+1)^2) := by
        apply sum_congr rfl
        intro j hj
        dsimp [a]
        push_cast
        congr 1
        ring
      _ ≤ _ := oddIndexMass M
  have htail := subsetTailMass P a (fun i hi => by dsimp [a]; positivity) hP
  have hsub : S.image Nat.primeFactors ⊆ P.powerset.erase ∅ := by
    intro t ht
    obtain ⟨m,hm,rfl⟩ := mem_image.mp ht
    obtain ⟨hm1,hmM,hmodd,hsq⟩ := hS m hm
    apply mem_erase.mpr
    refine ⟨?_,mem_powerset.mpr ?_⟩
    · intro he
      have h := Nat.prod_primeFactors_of_squarefree hsq
      rw [he,prod_empty] at h
      omega
    · intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      have hpM := (Nat.le_of_dvd (by omega : 0<m) hd).trans hmM
      have hpn : ¬2∣p := by
        intro hp2
        obtain ⟨k,hk⟩ := hp2.trans hd
        obtain ⟨l,hl⟩ := hmodd
        omega
      have hpodd : p%2=1 := by omega
      have h2 := hprime.two_le
      have h3 : 3≤p := by omega
      apply mem_image.mpr
      refine ⟨(p-3)/2,mem_range.mpr (by omega),?_⟩
      omega
  have hinj : Set.InjOn Nat.primeFactors (S: Set ℕ) := by
    intro m hm k hk he
    have h1 := Nat.prod_primeFactors_of_squarefree (hS m hm).2.2.2
    have h2 := Nat.prod_primeFactors_of_squarefree (hS k hk).2.2.2
    rw [he] at h1
    exact h1.symm.trans h2
  have hterm (m : ℕ) (hm : m∈S) :
      1/((m.totient:ℝ)^2) = ∏ p ∈ m.primeFactors,a p := by
    obtain ⟨hm1,hmM,hmodd,hsq⟩ := hS m hm
    have hphi := Nat.totient_mul_prod_primeFactors m
    rw [Nat.prod_primeFactors_of_squarefree hsq,mul_comm m] at hphi
    have hφ : m.totient = ∏ p∈m.primeFactors,(p-1) :=
      Nat.eq_of_mul_eq_mul_right (show 0<m by omega) hphi
    rw [hφ,Nat.cast_prod,← Finset.prod_pow]
    calc
      1 / (∏ p ∈ m.primeFactors, ((p-1:ℕ):ℝ)^2) =
          (∏ p ∈ m.primeFactors, (1:ℝ)) / (∏ p ∈ m.primeFactors, ((p-1:ℕ):ℝ)^2) := by simp
      _ = ∏ p ∈ m.primeFactors, a p := by
        rw [← Finset.prod_div_distrib]
        apply prod_congr rfl
        intro p hp
        have hp1 := (Nat.prime_of_mem_primeFactors hp).one_lt.le
        dsimp [a]
        rw [Nat.cast_sub hp1,Nat.cast_one]
  calc
    _ = ∑ m ∈ S,∏ p∈m.primeFactors,a p := sum_congr rfl hterm
    _ = ∑ t ∈ S.image Nat.primeFactors,∏ p∈t,a p := by
      rw [sum_image hinj]
    _ ≤ ∑ t ∈ P.powerset.erase ∅,∏ p∈t,a p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun t ht hnot => prod_nonneg (fun p hp => by dsimp [a]; positivity))
    _ ≤ _ := htail

end
end InnerFloorIndependentEulerMass
#print axioms InnerFloorIndependentEulerMass.oddIndexMass
#print axioms InnerFloorIndependentEulerMass.subsetTailMass

#print axioms InnerFloorIndependentEulerMass.oddSquarefreeTotientTail


namespace InnerFloorIndependentCross
noncomputable section

/-- Arithmetic conductor decay plus the constant real-zero gap yields an
arbitrarily large inverse-log saving. L is log of the target integer.
This is a scalar lemma, not a statement about a Dirichlet L-function. -/
theorem crossSaving (d L c k gap : ℝ)
    (hd : 1≤d) (hL : 1≤L) (hk : 0≤k) (hg : 0≤gap)
    (hgap : c≤gap*Real.log (d+2))
    (hbudget : k*Real.log L*(Real.log 3+2*k*Real.log L)≤c*L) :
    d^(-(1/2):ℝ)*Real.exp (-gap*L) ≤ L^(-k) := by
  have hdp : 0<d := by linarith
  have hLp : 0<L := by linarith
  have hld : 0≤Real.log d := Real.log_nonneg hd
  have hlL : 0≤Real.log L := Real.log_nonneg hL
  rw [Real.rpow_def_of_pos hdp,Real.rpow_def_of_pos hLp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  by_cases h : L^(2*k)≤d
  · have hlog := Real.log_le_log (Real.rpow_pos_of_pos hLp _) h
    rw [Real.log_rpow hLp] at hlog
    nlinarith only [hlog,mul_nonneg hg hLp.le]
  · have hpow : 1≤L^(2*k) := Real.one_le_rpow hL (by linarith)
    have hsmall : d+2≤3*L^(2*k) := by linarith [le_of_not_ge h]
    have hlog := Real.log_le_log (show 0<d+2 by linarith) hsmall
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (Real.rpow_pos_of_pos hLp _).ne',Real.log_rpow hLp] at hlog
    have h1 : k*Real.log L*Real.log (d+2)≤c*L :=
      (mul_le_mul_of_nonneg_left hlog (mul_nonneg hk hlL)).trans hbudget
    have h2 : c*L≤(gap*Real.log (d+2))*L := mul_le_mul_of_nonneg_right hgap hLp.le
    have h3 : k*Real.log L≤gap*L := by
      by_contra! hn
      have hh := mul_lt_mul_of_pos_right hn (Real.log_pos (show 1<d+2 by linarith))
      nlinarith only [h1,h2,hh]
    nlinarith only [h3,hld]

/-- Explicit sufficient budget in the preceding lemma, avoiding any
assumption about rates hidden in an asymptotic notation. -/
theorem crossBudget (L c k : ℝ) (hL : 1≤L) (hc : 0<c) (hk : 0≤k)
    (hlarge : (8*k+32*k^2)/c≤Real.sqrt L) :
    k*Real.log L*(Real.log 3+2*k*Real.log L)≤c*L := by
  let x := Real.sqrt (Real.sqrt L)
  have hL0 : 0≤L := by linarith
  have hx2 : x^2=Real.sqrt L := Real.sq_sqrt (Real.sqrt_nonneg L)
  have hx4 : x^4=L := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hx2,Real.sq_sqrt hL0]
  have hxs : 1≤x := by
    have h1 : 1≤Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
    exact by simpa [x] using Real.sqrt_le_sqrt h1
  have hxp : 0<x := by linarith
  have hl : 0≤Real.log L := Real.log_nonneg hL
  have hl4 : Real.log L≤4*x := by
    rw [←hx4,Real.log_pow]
    norm_num
    linarith [Real.log_le_sub_one_of_pos hxp]
  have h3 : Real.log 3≤2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  have ht : Real.log 3+2*k*Real.log L≤2+8*k*x := by nlinarith only [h3,mul_le_mul_of_nonneg_left hl4 hk]
  have hb : 0≤Real.log 3+2*k*Real.log L := by
    have := Real.log_nonneg (by norm_num : (1:ℝ)≤3)
    positivity
  have hbound : k*Real.log L*(Real.log 3+2*k*Real.log L)≤(8*k+32*k^2)*x^2 := by
    calc
      _ ≤ (k*(4*x))*(2+8*k*x) := mul_le_mul (mul_le_mul_of_nonneg_left hl4 hk) ht hb (by positivity)
      _ = 8*k*x+32*k^2*x^2 := by ring
      _ ≤ (8*k+32*k^2)*x^2 := by nlinarith only [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8) hk) (mul_nonneg hxp.le (sub_nonneg.mpr hxs))]
  have hcoef : 8*k+32*k^2≤c*Real.sqrt L := by
    have hh := (div_le_iff₀ hc).mp hlarge
    simpa [mul_comm] using hh
  calc
    _ ≤ _ := hbound
    _ ≤ c*Real.sqrt L*x^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
    _ = c*L := by rw [hx2,mul_assoc,←pow_two,Real.sq_sqrt hL0]

/-- All sufficiently large L satisfy the explicit scalar budget. -/
theorem eventualCrossSaving (c k : ℝ) (hc : 0<c) (hk : 0≤k) :
    ∃ L₀ : ℝ, 1≤L₀ ∧ ∀ L≥L₀, ∀ d gap : ℝ,
      1≤d → 0≤gap → c≤gap*Real.log (d+2) →
      d^(-(1/2):ℝ)*Real.exp (-gap*L)≤L^(-k) := by
  let a := max 1 ((8*k+32*k^2)/c)
  have ha : 1≤a := le_max_left _ _
  have ha0 : 0≤a := by linarith
  refine ⟨a^2,by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha)],?_⟩
  intro L hL d gap hd hg hgap
  have hL1 : 1≤L := (show 1≤a^2 by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha)]).trans hL
  have hs := Real.sqrt_le_sqrt hL
  rw [Real.sqrt_sq_eq_abs,abs_of_nonneg ha0] at hs
  exact crossSaving d L c k gap hd hL1 hk hg hgap
    (crossBudget L c k hL1 hc hk ((le_max_right _ _).trans hs))

end
end InnerFloorIndependentCross
#print axioms InnerFloorIndependentCross.crossSaving
#print axioms InnerFloorIndependentCross.crossBudget
#print axioms InnerFloorIndependentCross.eventualCrossSaving


namespace InnerFloorIndependentRealKernel
noncomputable section
open MeasureTheory
open scoped Interval

/-- Exact normalized L2-distance for the near-one power kernel versus one. -/
theorem powerKernel_sq_integral (b : ℝ) (hb : 1/2<b) :
    (∫ x in (0:ℝ)..1,(x^(b-1)-1)^2) =
      2*(1-b)^2/(b*(2*b-1)) := by
  have h1 : -1 < b-1 := by linarith
  have h2 : -1 < 2*b-2 := by linarith
  have hi1 : IntervalIntegrable (fun x:ℝ => x^(b-1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' h1
  have hi2 : IntervalIntegrable (fun x:ℝ => x^(2*b-2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' h2
  have hi0 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 := intervalIntegrable_const
  have he : (∫ x in (0:ℝ)..1,(x^(b-1)-1)^2) =
      ∫ x in (0:ℝ)..1, x^(2*b-2)-2*x^(b-1)+1 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0≤x := by simpa [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx.1
    have hpow : (x^(b-1))^2=x^(2*b-2) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hx0]
      congr 1
      norm_num
      ring
    dsimp only
    rw [sub_sq,hpow]
    ring
  rw [he,intervalIntegral.integral_add (hi2.sub (hi1.const_mul 2)) hi0,
    intervalIntegral.integral_sub hi2 (hi1.const_mul 2),intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl h2),integral_rpow (Or.inl h1)]
  simp only [Real.one_rpow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one]
  rw [Real.zero_rpow (by linarith : 2*b-2+1≠0),Real.zero_rpow (by linarith : b-1+1≠0)]
  rw [show 2*b-2+1=2*b-1 by ring,show b-1+1=b by ring]
  field_simp [show b≠0 by linarith,show 2*b-1≠0 by linarith]
  ring

/-- Quadratic upper bound on the squared L2 distance. -/
theorem powerKernel_sq_bound (b : ℝ) (hb : 3/4≤b) :
    (∫ x in (0:ℝ)..1,(x^(b-1)-1)^2) ≤ (16/3:ℝ)*(1-b)^2 := by
  rw [powerKernel_sq_integral b (by linarith)]
  have hbp : 0<b*(2*b-1) := mul_pos (by linarith) (by linarith)
  have hden : (3/8:ℝ)≤b*(2*b-1) := by
    calc
      _ = (3/4:ℝ)*(1/2) := by norm_num
      _ ≤ b*(2*b-1) := mul_le_mul hb (by linarith) (by norm_num) (by linarith)
  apply (div_le_iff₀ hbp).mpr
  nlinarith only [mul_nonneg (sq_nonneg (1-b)) (sub_nonneg.mpr hden)]

end
end InnerFloorIndependentRealKernel
#print axioms InnerFloorIndependentRealKernel.powerKernel_sq_integral
#print axioms InnerFloorIndependentRealKernel.powerKernel_sq_bound


namespace InnerFloorIndependentRelativeSign
open Finset
noncomputable section

/-- A robust positive main coefficient survives signed perturbations with
relative approximation and a strict bound on the absolute tail mass. -/
theorem weightedRelativeFloor {ι : Type*} (s : Finset ι)
    (W V a : ι → ℝ) (w v : ℝ)
    (hw : 0 ≤ w) (hv : (9/10:ℝ)*w ≤ v)
    (hW : ∀ i ∈ s, 0 ≤ W i ∧ W i ≤ w)
    (hV : ∀ i ∈ s, (9/10:ℝ)*W i ≤ V i ∧ V i ≤ (11/10:ℝ)*W i)
    (ha : ∑ i ∈ s, |a i| ≤ (2/3:ℝ)) :
    w/6 ≤ v + ∑ i ∈ s, a i * V i := by
  have ht : ∀ i ∈ s, -(|a i| * ((11/10:ℝ)*w)) ≤ a i * V i := by
    intro i hi
    have h0 : 0≤V i := (mul_nonneg (by norm_num) (hW i hi).1).trans (hV i hi).1
    have htop : V i ≤ (11/10:ℝ)*w := (hV i hi).2.trans
      (mul_le_mul_of_nonneg_left (hW i hi).2 (by norm_num))
    have hh := mul_le_mul (le_abs_self (-a i)) htop h0 (abs_nonneg (-a i))
    rw [abs_neg,neg_mul] at hh
    linarith only [hh]
  have hs := sum_le_sum ht
  rw [sum_neg_distrib,← sum_mul] at hs
  have ha' := mul_le_mul_of_nonneg_right ha (mul_nonneg (by norm_num : (0:ℝ)≤11/10) hw)
  linarith only [hs,ha',hv]

/-- Summing such blocks with nonnegative coefficients preserves the
one-sided positive margin without paying a cardinality factor. -/
theorem blockRelativeFloor {ι : Type*} (s : Finset ι)
    (w v c : ι → ℝ) (hc : ∀ i ∈ s, 0≤c i)
    (hv : ∀ i ∈ s, w i/6≤v i) :
    (∑ i ∈ s, c i*w i)/6 ≤ ∑ i ∈ s,c i*v i := by
  have hs := sum_le_sum (s:=s) (fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (hc i hi))
  calc
    _ = ∑ i ∈ s, c i*(w i/6) := by
      rw [sum_div]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := hs

end
end InnerFloorIndependentRelativeSign
#print axioms InnerFloorIndependentRelativeSign.weightedRelativeFloor
#print axioms InnerFloorIndependentRelativeSign.blockRelativeFloor




end
end PartII_RouteBResearch

namespace Conjectures.Goldbach

/-- Exact frozen statement registered for `L-goldbach-wide-remainder-inner-floor`. -/
def L_goldbach_wide_remainder_inner_floor_stmt : Prop :=
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n ∩ inner n)

/-- True single-gap closure for `L-goldbach-wide-remainder-inner-floor`:
    reduces the exact registered frozen statement unconditionally to the
    one-sided signed middle-band remainder floor
    `InnerFloorResearch.SignedMiddleRemainderFloor` (with 0 `sorry` and
    standard 3 axioms only). -/
theorem L_goldbach_wide_remainder_inner_floor_of_signedMiddleFloor
    (hSigned : InnerFloorResearch.SignedMiddleRemainderFloor) :
    L_goldbach_wide_remainder_inner_floor_stmt :=
  InnerFloorResearch.candidate_of_signedMiddleFloor hSigned

end Conjectures.Goldbach

#print axioms Conjectures.Goldbach.L_goldbach_wide_remainder_inner_floor_of_signedMiddleFloor
