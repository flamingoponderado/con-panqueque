import ConPanqueque.T.Ind.IndParams

/-!
# The block-shape records in the value heap

`readBlock` returns a `BlockShape` every later step of the inductive check reads.  The port keeps it in the
value heap, every record a heap block reached by a pointer (`cellA C o`):

* a constant (`IConstantVal`): the environment's own three words (`CVE`: name, level-parameter list, type);
* a member (`MemberShape`): `[cvT, declared, nIdx, ctors]`, `ctors` a block of `(constant, field count)` pairs;
* a recursor (`RecShape`): `[cvR, rP, mI, tgt, rules, isK]`, the rules in the environment's layout (`RulesE`);
* the shape: `[members, recs, nP, elim, resSort, large, isProp]`, `members` and `recs` blocks of pointers.

Each representation is stable under heap growth (`…_mono`), so a record built once stays readable.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Decl

/-- A pointer word to a heap cell. -/
def PtrTo (C : Ctx) (w : BitVec 64) (o : Nat) : Prop := w = cellA C o

/-- A constant at `o`. -/
def CVRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (cv : IConstantVal) : Prop := CVE C.HB H o cv

/-- A `(constant, field count)` list: block at `o` of `2·n` words, pointer then count. -/
def CtorsRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (cs : List (IConstantVal × Nat)) : Prop :=
  H[o]? = some (BitVec.ofNat 64 cs.length) ∧
    ∀ i (hi : i < cs.length), ∃ oc, H[o + 1 + 2 * i]? = some (cellA C oc) ∧ CVRep C H oc cs[i].1 ∧
      NatE H (o + 2 + 2 * i) cs[i].2

/-- A member at `o`. -/
def MemberRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (m : MemberShape) : Prop :=
  (∃ oc, H[o]? = some (cellA C oc) ∧ CVRep C H oc m.cvT) ∧
  (∃ od, H[o + 1]? = some (cellA C od) ∧ CVRep C H od m.declared) ∧
  NatE H (o + 2) m.nIdx ∧
  (∃ ol, H[o + 3]? = some (cellA C ol) ∧ CtorsRep C H ol m.ctors)

/-- A recursor at `o`. -/
def RecRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (r : RecShape) : Prop :=
  (∃ oc, H[o]? = some (cellA C oc) ∧ CVRep C H oc r.cvR) ∧
  NatE H (o + 1) r.rP ∧ NatE H (o + 2) r.mI ∧ NatE H (o + 3) r.tgt ∧
  (∃ w, H[o + 4]? = some w ∧ RulesE C.HB H w r.rules) ∧
  H[o + 5]? = some (boolW r.isK)

/-- A block of pointers to records of a kind. -/
def PtrsRep {α : Type} (C : Ctx) (H : List (BitVec 64)) (o : Nat) (Rep : Nat → α → Prop) (xs : List α) : Prop :=
  H[o]? = some (BitVec.ofNat 64 xs.length) ∧
    ∀ i (hi : i < xs.length), ∃ oi, H[o + 1 + i]? = some (cellA C oi) ∧ Rep oi xs[i]

/-- The shape at `o`. -/
def ShapeRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (p : BlockShape) : Prop :=
  (∃ om, H[o]? = some (cellA C om) ∧ PtrsRep C H om (MemberRep C H) p.members) ∧
  (∃ or_, H[o + 1]? = some (cellA C or_) ∧ PtrsRep C H or_ (RecRep C H) p.recs) ∧
  NatE H (o + 2) p.nP ∧ H[o + 3]? = some (Enc.idxW p.elim) ∧ H[o + 4]? = some (Enc.idxW p.resSort) ∧
  H[o + 5]? = some (boolW p.large) ∧ H[o + 6]? = some (boolW p.isProp)

section
variable {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H')
include hp

theorem cvRep_mono {o : Nat} {cv : IConstantVal} (h : CVRep C H o cv) : CVRep C H' o cv := cve_mono hp h

theorem ctorsRep_mono {o : Nat} {cs : List (IConstantVal × Nat)} (h : CtorsRep C H o cs) : CtorsRep C H' o cs :=
  ⟨get_prefix h.1 hp, fun i hi => let ⟨oc, h1, h2, h3⟩ := h.2 i hi
    ; ⟨oc, get_prefix h1 hp, cvRep_mono hp h2, natE_mono hp h3⟩⟩

theorem memberRep_mono {o : Nat} {m : MemberShape} (h : MemberRep C H o m) : MemberRep C H' o m := by
  obtain ⟨⟨oc, a1, a2⟩, ⟨od, b1, b2⟩, c, ⟨ol, d1, d2⟩⟩ := h
  exact ⟨⟨oc, get_prefix a1 hp, cvRep_mono hp a2⟩, ⟨od, get_prefix b1 hp, cvRep_mono hp b2⟩, natE_mono hp c,
    ⟨ol, get_prefix d1 hp, ctorsRep_mono hp d2⟩⟩

theorem recRep_mono {o : Nat} {r : RecShape} (h : RecRep C H o r) : RecRep C H' o r := by
  obtain ⟨⟨oc, a1, a2⟩, b, c, d, ⟨w, e1, e2⟩, f⟩ := h
  exact ⟨⟨oc, get_prefix a1 hp, cvRep_mono hp a2⟩, natE_mono hp b, natE_mono hp c, natE_mono hp d,
    ⟨w, get_prefix e1 hp, ConPanqueque.T.Decl.rulesE_mono hp e2⟩, get_prefix f hp⟩

theorem ptrsRep_mono {α : Type} {o : Nat} {Rep Rep' : Nat → α → Prop} (hR : ∀ oi a, Rep oi a → Rep' oi a)
    {xs : List α} (h : PtrsRep C H o Rep xs) : PtrsRep C H' o Rep' xs :=
  ⟨get_prefix h.1 hp, fun i hi => let ⟨oi, h1, h2⟩ := h.2 i hi; ⟨oi, get_prefix h1 hp, hR _ _ h2⟩⟩

theorem shapeRep_mono {o : Nat} {p : BlockShape} (h : ShapeRep C H o p) : ShapeRep C H' o p := by
  obtain ⟨⟨om, a1, a2⟩, ⟨or_, b1, b2⟩, c, d, e, f, g⟩ := h
  exact ⟨⟨om, get_prefix a1 hp, ptrsRep_mono hp (fun _ _ => memberRep_mono hp) a2⟩,
    ⟨or_, get_prefix b1 hp, ptrsRep_mono hp (fun _ _ => recRep_mono hp) b2⟩, natE_mono hp c, get_prefix d hp,
    get_prefix e hp, get_prefix f hp, get_prefix g hp⟩

end

end ConPanqueque.T.Ind
