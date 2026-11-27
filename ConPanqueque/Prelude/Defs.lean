import ConRon.Bridge.Frontend.Prepare

/-! # Handle-level notions of the override pass

`isVal`/`valName`: a value record (not a block) and its name handle; `keyOf`: a prelude record's key
handle; `keepW`: a stream record declaring no key; `OverW`: what the override pass establishes
of the stream `Q` against the prelude `P`. -/

open ConRon.Arena

namespace ConPanqueque.Prelude

/-- Not an inductive block. -/
def isVal : IDeclaration → Bool
  | .indDecl .. => false
  | _ => true

/-- A value record's name handle. -/
def valName : IDeclaration → NIdx
  | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv .. | .axiomDecl cv | .quotDecl _ cv => cv.name
  | .indDecl .. => default

theorem names_val {d : IDeclaration} (h : isVal d = true) : d.names = [valName d] := by
  cases d <;> simp_all [isVal, valName, IDeclaration.names]

/-- A prelude record's key handle. -/
def keyOf (p : IDeclaration) : NIdx := p.names.head?.getD default

/-- A stream record the pass keeps: it declares no key (con-ron's `declares`: any of its names). -/
def keepW (keys : List NIdx) (d : IDeclaration) : Bool := !(keys.any (fun k => d.names.contains k))

/-- The facts the pass establishes of the stream `Q` and the prelude `P`: a stream record declaring a
prelude record's key is that record, and no two stream records declare the same key. -/
structure OverW (Q P : List IDeclaration) : Prop where
  key : ∀ p ∈ P, p.names.head? = some (keyOf p)
  eq : ∀ d ∈ Q, ∀ p ∈ P, d.names.contains (keyOf p) = true → d = p
  uniq : ∀ i j (hi : i < Q.length) (hj : j < Q.length), i < j → ∀ p ∈ P,
    Q[i].names.contains (keyOf p) = true → Q[j].names.contains (keyOf p) = true → False

end ConPanqueque.Prelude
