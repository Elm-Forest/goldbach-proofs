"""Research-only port of pinned QRH source to Mathlib fc4f59e.
No target statements or axioms are changed. Apply to a fresh checkout.
"""
from pathlib import Path
import sys
root=Path(sys.argv[1])
def edit(name, changes):
 p=root/name;s=p.read_text()
 for old,new in changes:
  assert old in s,(name,old)
  print(name,'replacement count',s.count(old))
  s=s.replace(old,new)
 p.write_text(s)
def heartbeat(name):
 p=root/name;s=p.read_text()
 lines=s.splitlines(keepends=True)
 i=max(i for i,l in enumerate(lines) if l.startswith('import '))+1
 lines.insert(i,'\nset_option maxHeartbeats 10000000\n')
 p.write_text(''.join(lines))
edit('RellichKondrachov/MeasureTheory/Function/LpSpace/Restrict.lean',[
 ('(f := fun x : α => f x) hs).2 hf','(f := fun x : α => f x) hs.nullMeasurableSet).2 hf')
])
edit('OAI/NumberTheory/DirichletL/ThetaProduct.lean',[
 ('hPf.comp (by fun_prop) (fun x hx => mul_pos hu hx)',
  'hPf.comp (show ContinuousOn (fun x : ℝ => u*x) (Ioi 0) from (continuous_const.mul continuous_id).continuousOn) (fun x hx => mul_pos hu hx)'),
 ('hPg.comp (by fun_prop) (fun x hx => mul_pos (inv_pos.mpr hu) hx)',
  'hPg.comp (show ContinuousOn (fun x : ℝ => u⁻¹*x) (Ioi 0) from (continuous_const.mul continuous_id).continuousOn) (fun x hx => mul_pos (inv_pos.mpr hu) hx)'),
 ('(HurwitzZeta.continuousOn_evenKernel a)).comp (by fun_prop)',
  '(HurwitzZeta.continuousOn_evenKernel a)).comp (show ContinuousOn (fun x : ℝ => u*x) (Ioi 0) from (continuous_const.mul continuous_id).continuousOn)'),
 ('(HurwitzZeta.continuousOn_cosKernel a)).comp (by fun_prop)',
  '(HurwitzZeta.continuousOn_cosKernel a)).comp (show ContinuousOn (fun x : ℝ => u⁻¹*x) (Ioi 0) from (continuous_const.mul continuous_id).continuousOn)')
])
edit('OAI/NumberTheory/DirichletL/LogarithmicControl.lean',[
 ('    change dist w c < _\n    linarith\n  have h := Complex.norm_deriv_le',
  '    change dist w c < 2 - a - 2 * e\n    exact lt_of_le_of_lt hdist (by linarith only [hw\',hzn,he])\n  have h := Complex.norm_deriv_le')
])
for f in ['OAI/NumberTheory/DirichletL/ThetaProduct.lean',
          'OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean',
          'PrimeNumberTheoremAnd/Sobolev.lean']:
 heartbeat(f)

# Round 3: address the remaining concrete API changes and deeper Wiener
# obligations revealed by run 46037572856. No theorem statements changed.
edit('RellichKondrachov/MeasureTheory/Function/LpSpace/Restrict.lean',[
 ('(f := fun x : α => f x) hs).2 (Lp.memLp f)',
  '(f := fun x : α => f x) hs.nullMeasurableSet).2 (Lp.memLp f)'),
 ('(f := fun x : α => f x) hs)\n    -- Combine',
  '(f := fun x : α => f x) hs.nullMeasurableSet)\n    -- Combine')
])
edit('OAI/NumberTheory/DirichletL/ThetaProduct.lean',[
 ('    rw [heq, P.h_feq _ (mul_pos (inv_pos.mpr hu) hx),',
  '    have hxpos : 0 < x := hx\n    have hfeq := P.h_feq (u⁻¹ * x) (show 0 < u⁻¹ * x from mul_pos (inv_pos.mpr hu) hxpos)\n    rw [heq, hfeq,')
])
edit('PrimeNumberTheoremAnd/Wiener.lean',[
 ("  simp_rw [hG' e1, sub_mul, ← mul_assoc]",
  "  have heq := hG' (show ((σ' : ℂ) + (u : ℂ) * I) ∈ {s : ℂ | 1 < s.re} from e1)\n  simp_rw [heq, sub_mul, ← mul_assoc]"),
 ('    simp [mem_Ico_iff_div hx] ; tauto',
  '    intro n hn\n    have hnot : (n:ℝ) / x ∉ Ico a b := fun hm => hn ((mem_Ico_iff_div hx).2 hm)\n    rw [indicator_of_notMem hnot,mul_zero]'),
 ('inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))',
  'inter_mem_nhdsWithin _ (Iio_mem_nhds (show 0 < δ / 2 from div_pos hδ (by norm_num)))')
])
heartbeat('PrimeNumberTheoremAnd/Wiener.lean')
