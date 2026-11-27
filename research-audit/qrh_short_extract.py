"""Extract the exact reachable source modules for the pinned 23/24 QRH.
No theorem source is modified. Unresolved non-Mathlib imports fail closed.
The extracted project is for independent research replay, not a community PR.
"""
import hashlib, json, re, subprocess, sys
from pathlib import Path
from collections import deque
root, vendor, out = map(Path, sys.argv[1:4])
entry = 'OAI.NumberTheory.DirichletL.QRH'
rev = 'c388e88e6519d139ad2ca5571ef0c7fbf0e245b5'
vrev = '8bcf392d0ddc241a87fc8c3371273af704638f9b'
def git(repo,*args):
    return subprocess.check_output(['git','-C',str(repo),*args])
assert git(root,'rev-parse','HEAD').decode().strip()==rev
assert git(vendor,'rev-parse','HEAD').decode().strip()==vrev
def index(repo, revision, prefix=''):
    names = git(repo,'ls-tree','-r','--name-only','-z',revision).decode().split('\0')
    return {p[len(prefix):-5].replace('/','.') : p for p in names
            if p.startswith(prefix) and p.endswith('.lean') and not p.startswith(prefix+'./')}
src=index(root,rev,'lean/')
vend=index(vendor,vrev)
# Only use the explicitly pinned vendored dependency source, not another copy
# of an OAI module. Verify source branch is the chosen one.
vend={k:v for k,v in vend.items() if k.startswith(('RellichKondrachov.','PrimeNumberTheoremAnd.'))}
# Lean headers have nested comments; ignore comment contents before scanning.
def uncomment(s):
    pos=0; depth=0; buf=[]
    while pos<len(s):
        if s.startswith('/-',pos):
            depth+=1; buf.append('  '); pos+=2
        elif depth and s.startswith('-/',pos):
            depth-=1; buf.append('  '); pos+=2
        elif depth:
            buf.append('\n' if s[pos]=='\n' else ' '); pos+=1
        elif s.startswith('--',pos):
            stop=s.find('\n',pos)
            if stop<0: break
            pos=stop
        else:
            buf.append(s[pos]); pos+=1
    return ''.join(buf)
def imports(data):
    found=[]
    for line in uncomment(data.decode()).splitlines():
        line=line.strip()
        if not line or line in ('module','prelude'): continue
        m=re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
        if not m: break
        found.extend(m.group(1).split())
    return found
allowed={'Lean','Mathlib','Init','Std','Aesop','Batteries','Qq','ProofWidgets','Plausible','ImportGraph','LeanSearchClient'}
seen={}; edges={}; outside=set(); missing=set(); todo=deque([entry])
while todo:
    m=todo.popleft()
    if m in seen or m in outside or m in missing: continue
    if m in src:
        repo,revision,path=root,rev,src[m]
    elif m in vend:
        repo,revision,path=vendor,vrev,vend[m]
    elif m.split('.')[0] in allowed:
        outside.add(m); continue
    else:
        missing.add(m); continue
    data=git(repo,'show',revision+':'+path)
    p=out/(m.replace('.','/')+'.lean')
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(data)
    seen[m]={'repository':str(repo),'revision':revision,'source_path':path,
             'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),
             'lines':len(data.splitlines())}
    edges[m]=imports(data)
    todo.extend(edges[m])
manifest={'entry':entry,'revision':rev,'vendor_revision':vrev,
          'modules':len(seen),'bytes':sum(v['bytes'] for v in seen.values()),
          'lines':sum(v['lines'] for v in seen.values()),
          'external_imports':sorted(outside),'missing':sorted(missing),'files':seen,'edges':edges}
out.mkdir(parents=True,exist_ok=True)
(out/'short-closure.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps({k:v for k,v in manifest.items() if k not in ('files','edges','external_imports')},indent=2))
if missing: raise SystemExit('Unresolved modules: '+', '.join(sorted(missing)))
assert entry in seen
