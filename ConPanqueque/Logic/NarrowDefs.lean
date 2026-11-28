import ConPanqueque.Logic.Die

/-! # Narrowing local scopes: the transformation

`cake --pancake` keeps every local of the enclosing scopes live at every `while`, so the emitted
program narrows the scope of each `var x = c;` (a word constant) to the statements that need it.
`narrowT` works bottom-up:

* an `if` one of whose branches always leaves the function (`return …`, a tail call such as
  `return die();`) is flattened: `if c {A} else {B}` becomes `if c {A} else {skip}; B`, so the code
  after a failure check is no longer nested in a branch;
* each declaration `var x = c; P` (body already narrowed) is pushed into `P` (`push`): statements
  before the first use of `x` and after its last use move out of the scope, the scope is split
  where `x` is dead (its old value is never read: `dk`), it is dropped where `x` does not occur, and
  it is pushed into both branches of an `if` and into the body of another declaration.

The proof that the result behaves like the original is in `ConPanqueque/Logic/Narrow.lean`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

namespace ConPanqueque.Logic

mutual
/-- May the expression read the local `x`?  (Struct expressions: yes.) -/
def ev (x : MlS) : ExpHOL 64 → Bool
  | .const _ => false
  | .var .local y => decide (y = x)
  | .var .global _ => false
  | .load _ a => ev x a
  | .load32 a => ev x a
  | .loadByte a => ev x a
  | .op _ args => evs x args
  | .panop _ args => evs x args
  | .cmp _ a b => ev x a || ev x b
  | .shift _ a b => ev x a || ev x b
  | .baseAddr => false
  | .topAddr => false
  | .bytesInWord => false
  | _ => true
def evs (x : MlS) : List (ExpHOL 64) → Bool
  | [] => false
  | e :: es => ev x e || evs x es
end

/-- May the program touch the local `x` (read it, write it, declare it)?  Unknown statements: yes. -/
def occ (x : MlS) : ProgHOL 64 → Bool
  | .skip | .break | .continue | .tick => false
  | .dec y _ e b => decide (y = x) || ev x e || occ x b
  | .assign _ y e => decide (y = x) || ev x e
  | .store a v | .store32 a v | .storeByte a v => ev x a || ev x v
  | .seq a b => occ x a || occ x b
  | .ite c a b => ev x c || occ x a || occ x b
  | .while c b => ev x c || occ x b
  | .call none _ args => evs x args
  | .call (some (none, none)) _ args => evs x args
  | .call (some (some (_, y), none)) _ args => decide (y = x) || evs x args
  | .extCall _ a b c d => ev x a || ev x b || ev x c || ev x d
  | .return e => ev x e
  | _ => true

/-- How a program uses the old value of `x`: `kill` (overwritten before any read, on every path
that completes normally), `pass` (never read; the program may still write it), `dep` (may be read). -/
inductive DK | kill | pass | dep
  deriving DecidableEq, Repr

def DK.seq : DK → DK → DK
  | .kill, _ => .kill
  | .pass, d => d
  | .dep, _ => .dep

def DK.meet : DK → DK → DK
  | .kill, .kill => .kill
  | .dep, _ => .dep
  | _, .dep => .dep
  | _, _ => .pass

def dk (x : MlS) : ProgHOL 64 → DK
  | .skip | .break | .continue | .tick => .pass
  | .dec y _ e b => if ev x e then .dep else if y = x then .pass else dk x b
  | .assign k y e => if ev x e then .dep else if k = .local ∧ y = x then .kill else .pass
  | .store a v | .store32 a v | .storeByte a v => if ev x a || ev x v then .dep else .pass
  | .seq a b => (dk x a).seq (dk x b)
  | .ite c a b => if ev x c then .dep else (dk x a).meet (dk x b)
  | .while c b => if ev x c then .dep else if dk x b = .dep then .dep else .pass
  | .call none _ args => if evs x args then .dep else .pass
  | .call (some (none, none)) _ args => if evs x args then .dep else .pass
  | .call (some (some (k, y), none)) _ args =>
    if evs x args then .dep else if k = .local ∧ y = x then .kill else .pass
  | .extCall _ a b c d => if ev x a || ev x b || ev x c || ev x d then .dep else .pass
  | .return e => if ev x e then .dep else .pass
  | _ => .dep

/-- `dk` of a statement list, stopping at the first statement that decides it. -/
def dkL (x : MlS) : List (ProgHOL 64) → DK
  | [] => .pass
  | a :: l => match dk x a with
    | .pass => dkL x l
    | d => d

/-- The statements of a sequence. -/
def toL : ProgHOL 64 → List (ProgHOL 64)
  | .seq a b => toL a ++ toL b
  | .skip => []
  | p => [p]

def ofL : List (ProgHOL 64) → ProgHOL 64
  | [] => .skip
  | [p] => p
  | p :: l => .seq p (ofL l)

/-- Statements that never complete normally. -/
def aborts : ProgHOL 64 → Bool
  | .call none _ _ => true
  | .return _ => true
  | _ => false

/-- `if` with a leaving branch, flattened. -/
def flatIte (c : ExpHOL 64) (a b : ProgHOL 64) : ProgHOL 64 :=
  if aborts a then .seq (.ite c a .skip) b
  else if aborts b then .seq (.ite c .skip b) a
  else .ite c a b

/-- `var x = c; p` -/
def decC (x : MlS) (c : BitVec 64) (p : ProgHOL 64) : ProgHOL 64 := .dec x .one (.const c) p

mutual
/-- `var x = c; p`, with the declaration pushed in (`fuel` bounds the nesting depth). -/
def push : Nat → MlS → BitVec 64 → ProgHOL 64 → ProgHOL 64
  | 0, x, c, p => decC x c p
  | n + 1, x, c, p => if occ x p then ofL (pushA n x c [] (toL p)) else p

/-- The statement list of a scope: `acc` (reversed) is the open segment that must stay in the scope
of `x` because `x` is still live after it. -/
def pushA : Nat → MlS → BitVec 64 → List (ProgHOL 64) → List (ProgHOL 64) → List (ProgHOL 64)
  | _, _, _, [], [] => []
  | _, x, c, acc@(_ :: _), [] => [decC x c (ofL acc.reverse)]
  | n, x, c, [], a :: l =>
    if occ x a then
      if dkL x l = .dep then pushA n x c [a] l
      else push1 n x c a :: pushA n x c [] l
    else a :: pushA n x c [] l
  | n, x, c, acc@(_ :: _), a :: l =>
    if dkL x l = .dep then pushA n x c (a :: acc) l
    else decC x c (ofL (a :: acc).reverse) :: pushA n x c [] l

/-- One statement that uses `x`. -/
def push1 : Nat → MlS → BitVec 64 → ProgHOL 64 → ProgHOL 64
  | n, x, c, .ite e a b => if ev x e then decC x c (.ite e a b) else .ite e (push n x c a) (push n x c b)
  | n, x, c, .dec y sh e b =>
    if y ≠ x ∧ ev x e = false then .dec y sh e (push n x c b) else decC x c (.dec y sh e b)
  | _, x, c, p => decC x c p
end

def narrowFuel : Nat := 1000000

/-- Narrow every constant declaration of the program. -/
def narrowT : ProgHOL 64 → ProgHOL 64
  | .dec x .one (.const c) b => push narrowFuel x c (narrowT b)
  | .dec x sh e b => .dec x sh e (narrowT b)
  | .seq a b => .seq (narrowT a) (narrowT b)
  | .ite c a b => flatIte c (narrowT a) (narrowT b)
  | .while c b => .while c (narrowT b)
  | .call (some (r, some (eid, v, h))) f args => .call (some (r, some (eid, v, narrowT h))) f args
  | .decCall n sh f args k => .decCall n sh f args (narrowT k)
  | p => p

/-- A code-table entry with its body narrowed. -/
def narrowE (e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  (e.1, narrowT e.2.1, e.2.2)

def narrowEntries (l : List (MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))) :
    List (MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :=
  l.map (fun fe => (fe.1, narrowE fe.2))

end ConPanqueque.Logic
