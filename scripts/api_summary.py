#!/usr/bin/env python3
"""Print declaration signatures (no proofs) of Lean files: `api_summary.py FILE...`."""
import re, sys
start = re.compile(r'^(@\[[^\]]*\]\s*)?(protected |private |noncomputable |public |scoped |local )*(theorem|lemma|def|abbrev|instance|class|structure|inductive)\b')
for path in sys.argv[1:]:
    print(f"\n===== {path} =====")
    lines = open(path, encoding='utf-8').read().split('\n')
    i = 0
    while i < len(lines):
        if start.match(lines[i]):
            j = i
            buf = []
            while j < len(lines):
                l = lines[j]
                cut = None
                for tok in (':=', ' where', ' by'):
                    k = l.find(tok)
                    if k >= 0 and (cut is None or k < cut):
                        cut = k
                if l.startswith('  | ') or l.strip() == '':
                    break
                if cut is not None:
                    buf.append(l[:cut].rstrip()); break
                buf.append(l); j += 1
            print('\n'.join(b for b in buf if b.strip()))
            i = j + 1
        else:
            i += 1
