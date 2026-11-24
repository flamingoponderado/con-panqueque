import re, sys
src=open(sys.argv[1]).read()
loops=sys.argv[2].split(',')
wrap={'Nat':'.n','List Nat':'.l','String':'.s','Bool':'.b','HintsRec':'.h'}
proj={'Nat':'nat','List Nat':'list','String':'str','Bool':'bool','HintsRec':'hint'}
out=[]
for f in loops:
    body=src[src.index('def '+f+' '):]
    body=body[:body.index('\ndef ',5)]
    sig=body[:body.index(': ScanRes')]
    params=re.findall(r'\((\w+) : ([^)]+)\)',sig)
    params=[(n,t.strip()) for n,t in params if n not in ('b','i','wantMember','seen')]
    rty=re.search(r': ScanRes (\w+)',body).group(1)
    need=re.search(r'\(seen &&& (\d+)\) != \d+ then \.err ⟨i\.toNat, \.missingKey⟩',body).group(1)
    ctor=re.search(r'else \.ok (\(.*\)) \(i \+ 1\)',body).group(1)
    # key branches
    parts=re.split(r'\n\s*\| \.(k\w+) =>',body)
    keys=[]; kinds=[]
    for kname,br in zip(parts[1::2],parts[2::2]):
        bit=re.search(r'\(seen &&& (\d+)\) != 0',br).group(1)
        sc=re.search(r'(numEnd|scanBinderInfo|scanNatList|scanString|scanBool|scanHints) b v',br).group(1)
        call=re.search(r'%s b e false \(seen \|\|\| \d+\)(.*)'%f,br).group(1).strip()
        args=re.findall(r'\(readNatAt b v e\)|\S+',call)
        slot=None
        for j,(a,(pn,pt)) in enumerate(zip(args,params)):
            if a!=pn: slot=j
        if sc=='numEnd': act=f'.natSet {slot}' if slot is not None else '.natDrop'
        elif sc=='scanBinderInfo': act='.binder'
        elif sc=='scanNatList': act=f'.natList {slot}' if slot is not None else '.natListDrop'
        elif sc=='scanString': act=f'.str {slot}'
        elif sc=='scanBool': act=f'.bool {slot}' if slot is not None else '.boolDrop'
        elif sc=='scanHints': act=f'.hints {slot}'
        keys.append(f'(.{kname}, {bit}, {act})'); kinds.append((kname,sc))
    spec=f[0].lower()+f[1:].replace('Loop','Spec')
    out.append(f'def {spec} : ObjSpec := ⟨[{", ".join(keys)}], {need}⟩\n')
    pnames=' '.join(n for n,_ in params)
    ptys=' '.join(f'({n} : {t})' for n,t in params)
    slots=', '.join(f'{wrap[t]} {n}' for n,t in params)
    c=ctor
    for j,(n,t) in enumerate(params):
        c=re.sub(r'\b%s\b'%n, f'(sl.getD {j} default).{proj[t]}', c)
    c=re.sub(r'^\((\.\w+)', lambda m: '('+rty+m.group(1)[0:]+'', c) # qualify ctor
    c='('+rty+c[1:] if c.startswith('(.') else c
    us=' '.join(['_']*len(params))
    cases=''
    for kname,sc in kinds:
        tail=f'''               by_cases hie : i < e
               · rw [dif_pos hie, dif_pos hie]
                 have := USize.lt_iff_toNat_lt.mp hie
                 rw [ih _ (by omega) e false _ {us} rfl]
                 simp only [applyUpd, List.set] <;> rfl
               · rw [dif_neg hie, dif_neg hie]; rfl
'''
        if sc=='numEnd' or sc=='scanBinderInfo':
            zero = 'v' if sc=='numEnd' else '0'
            cases+=f'''        case {kname} =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize {sc} b v = e
          by_cases he : (e == {zero}) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
'''+tail.replace('               ','          ')
        else:
            cases+=f'''        case {kname} =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : {sc} b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
'''+tail.replace('               ','            ')
    out.append(f'''theorem {f}_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) {ptys}, b.size - i.toNat = msr →
      {f} b i wm seen {pnames} =
        srMap (fun sl => {c}) (objLoop {spec} b i wm seen [{slots}]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen {pnames} hn
    rw [{f}, objLoop]
    by_cases h : i < b.usize
    · rw [dif_pos h, dif_pos h]
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
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
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
@@CASES@@      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dif_neg h, dif_neg h]; rfl
'''.replace('@@CASES@@',cases))
print("\n".join(out))
