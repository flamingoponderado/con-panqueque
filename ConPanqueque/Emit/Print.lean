import ConPanqueque.Code.Table
import Flapjack.Parser

/-! # Printing Pancake source

`printProg`/`printFun` render `ProgHOL 64` in the concrete syntax `cake --pancake` reads.
Expressions are fully parenthesised; a declaration is printed as its own block so its scope is
exactly its body. Identifiers are prefixed (`v_` for variables, `f_` for functions) so no
name collides with a keyword. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

namespace ConPanqueque.Emit

def nameStr (m : MlS) : String := String.ofList (m.explode.map (fun b => Char.ofNat b.toNat))
def vname (m : MlS) : String := "v_" ++ nameStr m
def fname (m : MlS) : String := "f_" ++ nameStr m

def shapeStr : ShapeHOL → String
  | .one => "1"
  | .comb ss => "<" ++ ", ".intercalate (ss.map shapeStr) ++ ">"
  | .named n => nameStr n

def binStr : BinOp → String
  | .add => "+" | .sub => "-" | .and => "&" | .or => "|" | .xor => "^"

partial def expStr : ExpHOL 64 → String
  | .const w => s!"{w.toNat}"
  | .var _ x => vname x
  | .load sh a => s!"(lds {shapeStr sh} {expStr a})"
  | .loadByte a => s!"(ld8 {expStr a})"
  | .load32 a => s!"(ld32 {expStr a})"
  | .op o as => "(" ++ (" " ++ binStr o ++ " ").intercalate (as.map expStr) ++ ")"
  | .panop .mul [a, b] => s!"({expStr a} * {expStr b})"
  | .panop _ _ => "0"
  | .cmp .equal a b => s!"({expStr a} == {expStr b})"
  | .cmp .notEqual a b => s!"({expStr a} != {expStr b})"
  | .cmp .lower a b => s!"({expStr a} <+ {expStr b})"
  | .cmp .less a b => s!"({expStr a} < {expStr b})"
  | .cmp .notLower a b => s!"({expStr a} >=+ {expStr b})"
  | .cmp .notLess a b => s!"({expStr a} >= {expStr b})"
  | .cmp _ _ _ => "0"
  | .shift .lsl a b => s!"({expStr a} << {expStr b})"
  | .shift .lsr a b => s!"({expStr a} >>> {expStr b})"
  | .shift .asr a b => s!"({expStr a} >> {expStr b})"
  | .shift .ror a b => s!"({expStr a} #>> {expStr b})"
  | .baseAddr => "@base"
  | .topAddr => "@base"
  | .bytesInWord => "@biw"
  | _ => "0"

/-- A statement sequence, closed by `}`. -/
partial def progStr : ProgHOL 64 → String
  | .skip => "skip;"
  | .dec x sh e body => s!"\{ var {shapeStr sh} {vname x} = {expStr e}; {progStr body} };"
  | .assign _ x e => s!"{vname x} = {expStr e};"
  | .store a v => s!"st {expStr a}, {expStr v};"
  | .storeByte a v => s!"st8 {expStr a}, {expStr v};"
  | .store32 a v => s!"st32 {expStr a}, {expStr v};"
  | .seq p q => progStr p ++ " " ++ progStr q
  | .ite c p q => s!"if {expStr c} \{ {progStr p} } else \{ {progStr q} }"
  | .while c p => s!"while {expStr c} \{ {progStr p} }"
  | .break => "break;"
  | .continue => "continue;"
  | .call (some (some (_, x), none)) f args => s!"{vname x} = {fname f}({", ".intercalate (args.map expStr)});"
  | .call none f args => s!"return {fname f}({", ".intercalate (args.map expStr)});"
  | .call _ f args => s!"{fname f}({", ".intercalate (args.map expStr)});"
  | .extCall f c cl a al => s!"@{nameStr f}({expStr c}, {expStr cl}, {expStr a}, {expStr al});"
  | .return e => s!"return {expStr e};"
  | .tick => "tick;"
  | _ => "skip;"

def funStr (f : MlS) (ps : List (MlS × ShapeHOL)) (body : ProgHOL 64) (ret : ShapeHOL) : String :=
  s!"fun {shapeStr ret} {fname f}({", ".intercalate (ps.map (fun p => shapeStr p.2 ++ " " ++ vname p.1))}) \{\n  {progStr body}\n}\n"

end ConPanqueque.Emit
