import ConRon.Bridge.Frontend.Prepare

/-! # Handle-level notions of the override pass

`isVal`/`valName`: a value record (not a block) and its name handle; `keyOf`: a prelude record's key
handle; `keepW`: a stream record whose name is no key; `OverW`: what the override pass establishes
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

/-- A stream record the pass keeps: its name is no key. -/
def keepW (keys : List NIdx) (d : IDeclaration) : Bool := !(keys.contains (valName d))

/-- The facts the pass establishes of the stream `Q` and the prelude `P`. -/
structure OverW (Q P : List IDeclaration) : Prop where
  key : ∀ p ∈ P, p.names.head? = some (keyOf p)
  val : ∀ d ∈ Q, isVal d = true
  eq : ∀ d ∈ Q, ∀ p ∈ P, valName d = keyOf p → d = p
  uniq : ∀ i j (hi : i < Q.length) (hj : j < Q.length), i < j → (P.map keyOf).contains (valName Q[j]) = true →
    valName Q[i] ≠ valName Q[j]

end ConPanqueque.Prelude
