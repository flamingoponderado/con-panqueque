import ConPanqueque.Front.ScanKB

/-! # A record's fields from one scan

`recFun sp inits (vv (slotName k))` scans a record and returns one slot, so a declaration line read its six
fields with six scans.  `recFunKB sp inits r k₀ k₁ k₂` scans once, leaves slots `k₀ k₁ k₂` in the key buffer
and returns slot `r` (`RetK`); `recBodyKB_spec` is `recBody_spec` for all four. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

/-- The stores and the return after the object statement. -/
def kbTail (r k0 k1 k2 : Nat) : ProgHOL 64 :=
  .seq (kbStore 0 (vv (slotName k0))) (.seq (kbStore 1 (vv (slotName k1)))
    (.seq (kbStore 2 (vv (slotName k2))) (.return (vv (slotName r)))))

/-- `recKB(b, n, i)`: the record at `i`; `KB := [slot k₀, slot k₁, slot k₂]`; return slot `r`. -/
def recFunKB (sp : ObjSpec) (inits : List (BitVec 64)) (r k0 k1 k2 : Nat) : ProgHOL 64 :=
  decsOf (recLocals inits) (.seq (objStmt sp) (kbTail r k0 k1 k2))

/-- What the four words say: con-leche's record scanner accepts the record with slots `slots'`, and each word
is its slot. -/
def RecKOut (sp : ObjSpec) (b : ByteArray) (i : USize) (slots : List SVal) (r k0 k1 k2 : Nat)
    (w w0 w1 w2 : BitVec 64) : Prop :=
  ∃ j slots', RecOut sp b i slots j slots' ∧ j.toNat ≤ b.size + 64 ∧
    (∀ h : r < slots'.length, SlotOK b w slots'[r]) ∧ (∀ h : k0 < slots'.length, SlotOK b w0 slots'[k0]) ∧
    (∀ h : k1 < slots'.length, SlotOK b w1 slots'[k1]) ∧ (∀ h : k2 < slots'.length, SlotOK b w2 slots'[k2])

theorem recBodyKB_spec (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A KB : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)
    (hks : ∀ e ∈ sp.keys, ActOK nS e.2.2) (hn10 : nS ≤ 10)
    (i : USize) (hi : i.toNat ≤ b.size) (slots : List SVal) (hlen : slots.length = nS)
    (r k0 k1 k2 : Nat) (hr : r < nS) (h0 : k0 < nS) (h1 : k1 < nS) (h2 : k2 < nS)
    (u : PanSemStateFiniteExact 64 σ)
    (m0 : u.memory = t.memory) (d0 : u.memaddrs = t.memaddrs) (c0 : u.code = t.code) (g0 : u.globals = t.globals)
    (b0 : u.be = t.be)
    (hKB : u.globals.lookup gKb = some (.val (.word KB)))
    (hdom : ∀ j, j < 3 → u.memaddrs (KB + BitVec.ofNat 64 (8 * j)))
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (lg : u.locals.lookup sG = some (.val (.word 1)))
    (lw : u.locals.lookup sW = some (.val (.word 1)))
    (ls : u.locals.lookup sS = some (.val (.word 0)))
    (scr : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w)))
    (hsl : ∀ k (hk : k < slots.length), ∃ w, u.locals.lookup (slotName k) = some (.val (.word w)) ∧
      SlotOK b w slots[k]) :
    RetK KB u (.seq (objStmt sp) (kbTail r k0 k1 k2)) (RecKOut sp b i slots r k0 k1 k2) := by
  rcases objStmt_spec sp nS t A b hp hb hc hks hn10 i hi slots hlen u m0 d0 c0 g0 b0 lb ln li lg lw ls scr hsl with
    hs | ⟨hn, j, slots', hR, hI, hg⟩
  · exact Or.inl (seq_stop u _ _ hs)
  generalize he : evaluateHOLFiniteState u (objStmt sp) = res at hn hI hg
  obtain ⟨r1, r2⟩ := res
  simp only at hn hI hg
  subst hn
  obtain ⟨m', d', c', g', b', -, -, -, j', wm, seen, sl2, hj', hlen2, li', -, -, hsl2, br⟩ := hI
  have hR2 := (br.resolve_left (fun ⟨h1, _⟩ => by rw [hg] at h1; cases h1)).2
  simp only [ScanRes.ok.injEq] at hR2
  obtain ⟨rfl, rfl⟩ := hR2
  obtain ⟨w, hw, hok⟩ := hsl2 r (by omega)
  obtain ⟨w0, hw0, hok0⟩ := hsl2 k0 (by omega)
  obtain ⟨w1, hw1, hok1⟩ := hsl2 k1 (by omega)
  obtain ⟨w2, hw2, hok2⟩ := hsl2 k2 (by omega)
  unfold RetK kbTail
  rw [seq_normal _ he]
  simp only [kbStore]
  have hKB1 : r2.globals.lookup gKb = some (.val (.word KB)) := by rw [g']; rw [← g0]; exact hKB
  have hd1 : ∀ j, j < 3 → r2.memaddrs (KB + BitVec.ofNat 64 (8 * j)) := fun j hj => by
    rw [d']; rw [← d0]; exact hdom j hj
  rw [seq_normal _ (store_word r2 _ _ _ w0 (eval_kbAddr r2 KB 0 hKB1) (eval_vv r2 _ _ hw0) (hd1 0 (by decide)))]
  let u2 : PanSemStateFiniteExact 64 σ :=
    { r2 with memory := fun c => if c = KB + BitVec.ofNat 64 (8 * 0) then .word w0 else r2.memory c }
  rw [seq_normal _ (store_word u2 _ _ _ w1 (eval_kbAddr u2 KB 1 hKB1) (eval_vv u2 _ _ hw1) (hd1 1 (by decide)))]
  let u3 : PanSemStateFiniteExact 64 σ :=
    { u2 with memory := fun c => if c = KB + BitVec.ofNat 64 (8 * 1) then .word w1 else u2.memory c }
  rw [seq_normal _ (store_word u3 _ _ _ w2 (eval_kbAddr u3 KB 2 hKB1) (eval_vv u3 _ _ hw2) (hd1 2 (by decide)))]
  let u4 : PanSemStateFiniteExact 64 σ :=
    { u3 with memory := fun c => if c = KB + BitVec.ofNat 64 (8 * 2) then .word w2 else u3.memory c }
  have hw4 : u4.locals.lookup (slotName r) = some (.val (.word w)) := hw
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv u4 (slotName r) _ hw4
  refine Or.inr ⟨w, w0, w1, w2, q1, ⟨j, slots', hR, hj', fun _ => hok, fun _ => hok0, fun _ => hok1, fun _ => hok2⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [q2]; show u4.memory = _
    funext c; simp only [u4, u3, u2, kbSt]; rw [m', m0]
  · rw [q3]; exact d'.trans d0.symm
  · rw [q4]; exact g'.trans g0.symm
  · rw [q5]; exact c'.trans c0.symm
  · rw [q6]; exact b'.trans b0.symm

/-- The definition record's slots from one scan: slot `r` returned, slots `k₀ k₁ k₂` in the key buffer. -/
theorem defKB_sound (t : PanSemStateFiniteExact 64 σ) (A KB : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (hKB : t.globals.lookup gKb = some (.val (.word KB)))
    (hdom : ∀ j, j < 3 → t.memaddrs (KB + BitVec.ofNat 64 (8 * j)))
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (r k0 k1 k2 : Nat) (hr : r < 6) (h0 : k0 < 6) (h1 : k1 < 6) (h2 : k2 < 6)
    (d : ConLeche.Frontend.DeclRec) (e0 : USize) (hd : ConLeche.Frontend.scanDefDecl b i = .ok d e0) :
    RetK KB t (recFunKB scanDefDeclSpec [BitVec.ofNat 64 listSentinel, BitVec.ofNat 64 listSentinel, 0,
        BitVec.ofNat 64 listSentinel, 0, 0] r k0 k1 k2)
      (fun w w0 w1 w2 => ∃ slots', KindsOK [4, 1, 0, 2, 0, 0] slots' ∧
        d = (fun sl => (ConLeche.Frontend.DeclRec.defn ⟨(sl.getD 2 default).nat, (sl.getD 1 default).list,
          (sl.getD 4 default).nat⟩ (sl.getD 5 default).nat (sl.getD 0 default).hint (sl.getD 3 default).str)) slots' ∧
        (∀ h : r < slots'.length, SlotOK b w slots'[r]) ∧ (∀ h : k0 < slots'.length, SlotOK b w0 slots'[k0]) ∧
        (∀ h : k1 < slots'.length, SlotOK b w1 slots'[k1]) ∧ (∀ h : k2 < slots'.length, SlotOK b w2 slots'[k2])) := by
  unfold recFunKB
  apply retK_decsOf
  have hlk := recEntry_lookup [BitVec.ofNat 64 listSentinel, BitVec.ofNat 64 listSentinel, 0, BitVec.ofNat 64 listSentinel, 0, 0] t
  have hks : ∀ e ∈ scanDefDeclSpec.keys, ActOK 6 e.2.2 := by simp [scanDefDeclSpec, ActOK]
  have e := recBodyKB_spec (σ := σ) scanDefDeclSpec 6 t A KB b hp hb hc hks (by decide) i hi
    [.h (.regular 0), .l [], .n 0, .s "", .n 0, .n 0] rfl r k0 k1 k2 hr h0 h1 h2
    ((recLocals [BitVec.ofNat 64 listSentinel, BitVec.ofNat 64 listSentinel, 0, BitVec.ofNat 64 listSentinel, 0, 0]).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t) (foldl_setVar_memory _ _) rfl rfl rfl rfl
    hKB hdom
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]; exact lb)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]; exact ln)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]; exact li)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2])
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]⟩)
    (by intro k hk; simp only [List.length_cons, List.length_nil] at hk
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2], by simp [SlotOK, natCap, bw, listSentinel]⟩
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2], by simp [SlotOK, natCap, bw, listSentinel]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2], by simp [SlotOK, natCap, bw, listSentinel]⟩
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2], by simp [SlotOK, natCap, bw, listSentinel]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2], by simp [SlotOK, natCap, bw, listSentinel]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2], by simp [SlotOK, natCap, bw, listSentinel]⟩)
  rcases e with hs | ⟨w, w0, w1, w2, q1, ⟨j, slots', hro, -, hsr, hs0, hs1, hs2⟩, q2, q3, q4, q5, q6⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, w0, w1, w2, q1, ?_, q2, q3, q4, q5, q6⟩
  have hro' := hro
  unfold RecOut at hro'
  split at hro'
  · rename_i hbyte
    have hs : ConLeche.Frontend.scanDefDecl b i = .ok ((fun sl => (ConLeche.Frontend.DeclRec.defn ⟨(sl.getD 2 default).nat, (sl.getD 1 default).list, (sl.getD 4 default).nat⟩ (sl.getD 5 default).nat (sl.getD 0 default).hint (sl.getD 3 default).str)) slots') j := by
      rw [ConLeche.Frontend.scanDefDecl, scanDefDeclLoop_eq b _ (i + 1) true 0 (.regular 0) [] 0 "" 0 0 rfl, ite_eq_left hbyte, hro']; rfl
    rw [hd] at hs
    simp only [ConLeche.Frontend.ScanRes.ok.injEq] at hs
    have hsp : SpecKinds scanDefDeclSpec [4, 1, 0, 2, 0, 0] := by
      intro e he sl kd hw
      simp only [scanDefDeclSpec, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [VAct.wr, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hw <;>
        obtain ⟨rfl, rfl⟩ := hw <;> rfl
    have hK0 : KindsOK [4, 1, 0, 2, 0, 0] [.h (.regular 0), .l [], .n 0, .s "", .n 0, .n 0] := by
      refine ⟨rfl, fun k hk => ?_⟩
      simp only [List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    exact ⟨slots', objLoop_kinds scanDefDeclSpec [4, 1, 0, 2, 0, 0] hsp b _ (i + 1) true 0 [.h (.regular 0), .l [], .n 0, .s "", .n 0, .n 0] rfl hK0 slots' j hro', hs.1,
      hsr, hs0, hs1, hs2⟩
  · simp at hro'

end ConPanqueque.Front
