import ConPanqueque.Emit.Print

/-! # Round-trip check of the printer

`rename` applies the printer's identifier prefixes to an AST; `norm` flattens sequences and drops
`skip`. `roundTrip` parses the printed functions back with flapjack's parser and compares each body
with the renamed original, after normalisation. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

namespace ConPanqueque.Emit

def rn (p : String) (m : MlS) : MlS := ofString (p ++ nameStr m)

partial def renameE : ExpHOL 64 → ExpHOL 64
  | .var k x => .var k (rn "v_" x)
  | .load sh a => .load sh (renameE a)
  | .loadByte a => .loadByte (renameE a)
  | .load32 a => .load32 (renameE a)
  | .op o as => .op o (as.map renameE)
  | .panop o as => .panop o (as.map renameE)
  | .cmp o a b => .cmp o (renameE a) (renameE b)
  | .shift o a b => .shift o (renameE a) (renameE b)
  | e => e

partial def renameP : ProgHOL 64 → ProgHOL 64
  | .dec x sh e b => .dec (rn "v_" x) sh (renameE e) (renameP b)
  | .assign k x e => .assign k (rn "v_" x) (renameE e)
  | .store a v => .store (renameE a) (renameE v)
  | .storeByte a v => .storeByte (renameE a) (renameE v)
  | .store32 a v => .store32 (renameE a) (renameE v)
  | .seq p q => .seq (renameP p) (renameP q)
  | .ite c p q => .ite (renameE c) (renameP p) (renameP q)
  | .while c p => .while (renameE c) (renameP p)
  | .call (some (some (k, x), none)) f as => .call (some (some (k, rn "v_" x), none)) (rn "f_" f) (as.map renameE)
  | .call i f as => .call i (rn "f_" f) (as.map renameE)
  | .extCall f c cl a al => .extCall f (renameE c) (renameE cl) (renameE a) (renameE al)
  | .return e => .return (renameE e)
  | p => p

instance : Inhabited (ProgHOL 64) := ⟨.skip⟩

/-- Left-nested chains of one operator as one `op` (both mean the same left fold). -/
partial def normE : ExpHOL 64 → ExpHOL 64
  | .op o as =>
    let as := as.map normE
    match as with
    | .op o' xs :: ys => if o' == o then .op o (xs ++ ys) else .op o as
    | _ => .op o as
  | .load sh a => .load sh (normE a)
  | .loadByte a => .loadByte (normE a)
  | .load32 a => .load32 (normE a)
  | .panop o as => .panop o (as.map normE)
  | .cmp o a b => .cmp o (normE a) (normE b)
  | .shift o a b => .shift o (normE a) (normE b)
  | e => e

partial def normP : ProgHOL 64 → ProgHOL 64
  | .dec x sh e b => .dec x sh (normE e) (normP b)
  | .assign k x e => .assign k x (normE e)
  | .store a v => .store (normE a) (normE v)
  | .storeByte a v => .storeByte (normE a) (normE v)
  | .store32 a v => .store32 (normE a) (normE v)
  | .seq p q => .seq (normP p) (normP q)
  | .ite c p q => .ite (normE c) (normP p) (normP q)
  | .while c p => .while (normE c) (normP p)
  | .call i f as => .call i f (as.map normE)
  | .extCall f c cl a al => .extCall f (normE c) (normE cl) (normE a) (normE al)
  | .return e => .return (normE e)
  | p => p

def rebuild : List (ProgHOL 64) → ProgHOL 64
  | [] => .skip
  | [p] => p
  | p :: ps => .seq p (rebuild ps)

/-- The statements of a sequence, `skip` dropped. -/
partial def flat : ProgHOL 64 → List (ProgHOL 64)
  | .seq p q => flat p ++ flat q
  | .skip => []
  | .dec x sh e b => [.dec x sh e (rebuild (flat b))]
  | .ite c p q => [.ite c (rebuild (flat p)) (rebuild (flat q))]
  | .while c p => [.while c (rebuild (flat p))]
  | p => [p]

def norm (p : ProgHOL 64) : ProgHOL 64 := rebuild (flat (normP p))

/-- Compare the parsed functions with the originals; return the names that differ. -/
def roundTrip (src : String) (es : List (MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))) :
    Except String (List String) := do
  let ds ← match Flapjack.Parser.parseTopDecs (BitVec.ofInt 64) src with
    | .ok ds => pure ds
    | .error errs => throw s!"parse errors: {(errs.take 3).map (fun e => e.message)}"
  let funs := ds.filterMap (fun d => match declToHOL (width := 64) d with
    | .function f => some (nameStr f.name, f)
    | _ => none)
  let mut bad : List String := []
  for (f, ps, b, _) in es do
    match funs.lookup ("f_" ++ nameStr f) with
    | none => bad := ("missing " ++ nameStr f) :: bad
    | some fd =>
      let lhs := toString (repr (norm fd.body))
      let rhs := toString (repr (norm (renameP b)))
      let pOK := fd.params.map (fun p => nameStr p.1) == ps.map (fun p => "v_" ++ nameStr p.1)
      if lhs != rhs || !pOK then bad := nameStr f :: bad
  return bad

end ConPanqueque.Emit
