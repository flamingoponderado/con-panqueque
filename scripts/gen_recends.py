import re, sys
src=open(sys.argv[1]).read()
kinds=[('scanStrName','scanStrNameLoop','NameRec',['0','0','""']),
       ('scanNumName','scanNumNameLoop','NameRec',['0','0','0']),
       ('scanLamExpr','scanLamExprLoop','ExprRec',['0','0','0']),
       ('scanForallExpr','scanForallExprLoop','ExprRec',['0','0','0']),
       ('scanLetExpr','scanLetExprLoop','ExprRec',['0','0','0','0']),
       ('scanConstExpr','scanConstExprLoop','ExprRec',['0','0','[]']),
       ('scanProjExpr','scanProjExprLoop','ExprRec',['0','0','0','0']),
       ('scanDefDecl','scanDefDeclLoop','DeclRec',['0','(.regular 0)','[]','0','""','0','0']),
       ('scanThmDecl','scanThmDeclLoop','DeclRec',['0','[]','0','0','0']),
       ('scanOpaqueDecl','scanOpaqueDeclLoop','DeclRec',['0','false','[]','0','0','0'])]
out=[]
simpset="simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]"
for scan,loop,rty,args in kinds:
    body=src[src.index('def '+loop+' '):]
    sig=body[:body.index(': ScanRes')]
    params=re.findall(r'\((\w+) : ([^)]+)\)',sig)
    params=[(n,t.strip()) for n,t in params if n not in ('b','i','wantMember','seen')]
    initargs=args[1:]  # first arg is seen=0
    assert len(initargs)==len(params),(scan,initargs,params)
    sv=[]; words=[]; okt=[]
    for (n,t),a in zip(params,initargs):
        if t=='Nat': sv.append(f'.n {a}'); words.append('0'); okt.append('simp [SlotOK, natCap]')
        elif t=='List Nat': sv.append('.l []'); words.append('BitVec.ofNat 64 listSentinel'); okt.append('simp [SlotOK]')
        elif t=='String': sv.append('.s ""'); words.append('BitVec.ofNat 64 listSentinel'); okt.append('simp [SlotOK]')
        elif t=='Bool': sv.append('.b false'); words.append('0'); okt.append('simp [SlotOK, bw]')
        elif t=='HintsRec': sv.append(f'.h {a}'); words.append('0'); okt.append('simp [SlotOK]')
    n=len(params)
    spec=scan[0].lower()+scan[1:]+'Spec'
    ks=" ∨ ".join(f"k = {k}" for k in range(n))
    cases=" | ".join("rfl" for _ in range(n))
    slotbullets="\n".join(f"        · exact ⟨{w}, by rw [hlk]; {simpset}, by simp [SlotOK, natCap, bw, listSentinel]⟩" for w in words)
    out.append(f'''theorem {scan[4:].lower()}End_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t (recFun {spec} [{", ".join(words)}] (vv sI)) (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧
      ∃ r : {rty}, {scan} b i = .ok r j) := by
  unfold recFun
  apply retP_decsOf
  have hlk := recEntry_lookup [{", ".join(words)}] t
  have hks : ∀ e ∈ {spec}.keys, ActOK {n} e.2.2 := by simp [{spec}, ActOK]
  have e := recBody_spec (σ := σ) {spec} {n} t A b hp hb hc hks (by decide) i hi [{", ".join(sv)}] rfl sI (Or.inl rfl)
    ((recLocals [{", ".join(words)}]).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t) rfl rfl rfl rfl rfl
    (by rw [hlk]; {simpset}; exact lb)
    (by rw [hlk]; {simpset}; exact ln)
    (by rw [hlk]; {simpset}; exact li)
    (by rw [hlk]; {simpset})
    (by rw [hlk]; {simpset})
    (by rw [hlk]; {simpset})
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by rw [hlk]; {simpset}⟩)
    (by intro k hk; simp only [List.length_cons, List.length_nil] at hk
        rcases (show {ks} by omega) with {cases}
{slotbullets})
  refine retP_mono e ?_
  rintro w ⟨j, slots', hro, hw, -⟩
  refine ⟨j, hw rfl, ?_⟩
  unfold RecOut at hro
  rw [{scan}, {loop}_eq b _ (i + 1) true 0 {" ".join(initargs)} rfl]
  split at hro
  · rename_i hbyte; rw [if_pos hbyte, hro]; exact ⟨_, rfl⟩
  · simp at hro
''')
print("\n".join(out))
