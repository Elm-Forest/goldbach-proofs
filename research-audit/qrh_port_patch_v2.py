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
 lines.insert(i,'\nset_option maxHeartbeats 2000000\n')
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
