import Conjectures.Goldbach.DyadicCellShortPrimeFloor

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
