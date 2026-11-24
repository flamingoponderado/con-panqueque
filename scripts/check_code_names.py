#!/usr/bin/env python3
"""Check the code-table requirements for conflicts.

Input: the dump written by scripts/CodeScan.lean (`name ||| rhs` leaves separated by "@@").
Reports (1) a function constant required with syntactically different bodies, after
normalising `pmap ps` to `List.map (fun p => (p, one)) ps`; (2) two required constants whose
`ofString` literal is the same string (a real clash when their bodies differ).
"""
import sys, re, os, collections
dump = open(sys.argv[1]).read().split("\n@@\n")
lits = {}
for root, _, fs in os.walk('ConPanqueque'):
    for f in fs:
        if not f.endswith('.lean'): continue
        cur = []
        for line in open(os.path.join(root, f)):
            m = re.match(r'namespace (\S+)', line)
            if m: cur.append(m.group(1)); continue
            m = re.match(r'end (\S+)', line)
            if m and cur and cur[-1] == m.group(1): cur.pop(); continue
            m = re.match(r'def (\w+) *(?::[^:=]*)?:= *ofString "([^"]*)"', line)
            if m: lits['.'.join(cur + [m.group(1)])] = m.group(2)
req = collections.defaultdict(set)
for l in dump:
    if '|||' not in l: continue
    n, b = l.split('|||', 1)
    n = ' '.join(n.split()); b = ' '.join(b.split())
    b = re.sub(r'ConPanqueque\.T\.Knot\.pmap (\S+|\[[^\]]*\])', r'List.map (fun p => (p, Flapjack.Pancake.PanLang.ShapeHOL.one)) \1', b)
    req[n].add(b)
bad = 0
for n, bs in req.items():
    if len(bs) > 1: print('BODIES', n, *bs, sep='\n  '); bad += 1
bylit = collections.defaultdict(list)
for n in req:
    if n in lits: bylit[lits[n]].append(n)
for s, ns in bylit.items():
    if len(ns) > 1: print('SAME STRING', repr(s), ns); bad += 1
print(len(req), 'required functions,', bad, 'problems')
