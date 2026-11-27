# Generates the record-loop part of ConPanqueque/Scan/IndSpec.lean (specs, builders, *_eq).
# Usage: python3 scripts/gen_indspec.py deps/con-leche/ConLeche/Frontend/Scan/Fast.lean scanRuleLoop,scanIndTypeLoop,scanIndCtorLoop,scanIndRecLoop,scanIndDeclLoop
# (the committed file was then adjusted by hand: the `}` case and `<;> try rfl` tails).
import re, sys
src=open(sys.argv[1]).read()
# loop name -> (spec name, record type, build name)
cfg={
 'scanRuleLoop':('ruleSpec','RuleRec','ruleOf',False),
 'scanIndTypeLoop':('indTypeSpec','IndTypeRec','indTypeOf',False),
 'scanIndCtorLoop':('indCtorSpec','IndCtorRec','indCtorOf',False),
 'scanIndRecLoop':('indRecSpec','IndRecRec','indRecOf',True),
 'scanIndDeclLoop':('indDeclSpec','DeclRec','indDeclOf',True),
}
# list-of-record scanners: scanner -> (fid, unit scanner)
subs={'scanRules':(0,'scRulesU'),'scanIndCtors':(1,'scCtorsU'),'scanIndRecs':(2,'scRecsU'),'scanIndTypes':(3,'scTypesU')}
listty={'List RuleRec':'scanRules','List IndCtorRec':'scanIndCtors','List IndRecRec':'scanIndRecs','List IndTypeRec':'scanIndTypes'}
wrap={'Nat':'.n','List Nat':'.l','String':'.s','Bool':'.b','HintsRec':'.h'}
proj={'Nat':'nat','List Nat':'list','String':'str','Bool':'bool','HintsRec':'hint'}
out=[]
for f in sys.argv[2].split(','):
    spec,rty,bname,useb=cfg[f]
    body=src[src.index('def '+f+' '):]
    body=body[:body.index('\ndef ',5)]
    sig=body[:body.index(': ScanRes')]
    params=re.findall(r'\((\w+) : ([^)]+)\)',sig)
    params=[(n,t.strip()) for n,t in params if n not in ('b','i','wantMember','seen')]
    need=re.search(r'\(seen &&& (\d+)\) != \d+ then \.err ⟨i\.toNat, \.missingKey⟩',body).group(1)
    ctor=re.search(r'else \.ok (\(.*\)) \(i \+ 1\)',body).group(1)
    parts=re.split(r'\n\s*\| \.(k\w+) =>',body)
    keys=[]; kinds=[]
    for kname,br in zip(parts[1::2],parts[2::2]):
        bit=re.search(r'\(seen &&& (\d+)\) != 0',br).group(1)
        sc=re.search(r'(numEnd|scanBinderInfo|scanNatList|scanString|scanBool|scanHints|scanRules|scanIndCtors|scanIndRecs|scanIndTypes) b v',br).group(1)
        call=re.search(r'%s b e false \(seen \|\|\| \d+\)(.*)'%f,br,re.S).group(1).strip()
        call=' '.join(call.split('\n')[0:2]) if call.endswith('ty') is False else call
        call=' '.join(call.split())
        args=re.findall(r'\(some \(readNatAt b v e\)\)|\(readNatAt b v e\)|\S+',call)
        args=args[:len(params)]
        slot=None
        for j,(a,(pn,pt)) in enumerate(zip(args,params)):
            if a!=pn: slot=j
        if sc=='numEnd': act=f'.natSet {slot}' if slot is not None else '.natDrop'
        elif sc=='scanNatList': act=f'.natList {slot}' if slot is not None else '.natListDrop'
        elif sc=='scanBool': act=f'.bool {slot}' if slot is not None else '.boolDrop'
        elif sc in subs: act=f'.sub {subs[sc][0]} {subs[sc][1]} {slot}'
        else: raise Exception(sc)
        keys.append(f'(.{kname}, {bit}, {act})'); kinds.append((kname,sc))
    out.append(f'def {spec} : ObjSpec := ⟨[{", ".join(keys)}], {need}⟩\n')
    # binders / lhs args / slots / build
    binders=[]; lhs=[]; slots=[]; ivars=[]
    c=ctor
    for j,(n,t) in enumerate(params):
        if t in listty:
            binders.append(f'(p{n} : Nat)'); lhs.append(f'(rescanL {listty[t]} b p{n})'); slots.append(f'.p p{n}'); ivars.append('p'+n)
            c=re.sub(r'\b%s\b'%n, f'(rescanL {listty[t]} b (sl.getD {j} default).pos)', c)
        elif t=='Option Nat':
            binders.append(f'({n} : Option Nat)'); lhs.append(n); slots.append(f'optSV {n}'); ivars.append(n)
            c=re.sub(r'\b%s\b'%n, f'(sl.getD {j} default).opt', c)
        else:
            binders.append(f'({n} : {t})'); lhs.append(n); slots.append(f'{wrap[t]} {n}'); ivars.append(n)
            c=re.sub(r'\b%s\b'%n, f'(sl.getD {j} default).{proj[t]}', c)
    bsig='(b : ByteArray) ' if useb else ''
    bapp=f'{bname} b' if useb else bname
    out.append(f'def {bname} {bsig}(sl : List SVal) : {rty} := {c}\n')
    us=' '.join(['_']*len(params))
    cases=''
    for kname,sc in kinds:
        tail=lambda pre: f'''by_cases hie : i < e
· rw [dite_eq_left hie, dite_eq_left hie]
  have := USize.lt_iff_toNat_lt.mp hie
  rw [{pre}ih _ (by omega) e false _ {us} rfl]
  simp only [applyUpd, List.set] <;> rfl
· rw [dite_eq_right hie, dite_eq_right hie]; rfl'''
        def ind(s,k): return '\n'.join(' '*k+l for l in s.split('\n'))
        if sc=='numEnd':
            cases+=f'''        case {kname} =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
'''+ind(tail(''),10)+'\n'
        elif sc in subs:
            cases+=f'''        case {kname} =>
          split
          · simp [srMap]
          simp only [stepVal, {subs[sc][1]}]
          cases hx : {sc} b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only [srMap]
'''+ind(tail('← rescanL_of hx, '),12)+'\n'
        else:
            cases+=f'''        case {kname} =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : {sc} b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
'''+ind(tail(''),12)+'\n'
    out.append(f'''theorem {f}_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) {" ".join(binders)}, b.size - i.toNat = msr →
      {f} b i wm seen {" ".join(lhs)} =
        srMap ({bapp}) (objLoop {spec} b i wm seen [{", ".join(slots)}]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen {" ".join(ivars)} hn
    rw [{f}, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ {us} rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, {spec}]
          split <;> simp_all [srMap, {bname}, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint, SVal.pos, opt_optSV]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ {us} rfl
        · simp [srMap]
      have n44 : (c == 44) = false := beq_eq_false_iff_ne.mpr h44
      simp only [n44, Bool.false_eq_true, ↓reduceIte]
      by_cases h34 : c = 34
      · subst h34
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp [srMap]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        generalize keyEnd b (i + 1) = ke
        by_cases hk0 : (ke == 0) = true
        · simp [hk0, srMap]
        simp only [hk0, Bool.false_eq_true, ↓reduceIte]
        generalize valueAt b i ke = v
        by_cases hv : (v == i) = true
        · simp [hv, srMap]
        simp only [hv, Bool.false_eq_true, ↓reduceIte]
        generalize keyAt b i (ke - (i + 1)) = k
        cases k <;> simp only [lookupKey, {spec}, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
{cases}      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl
''')
print("\n".join(out))
