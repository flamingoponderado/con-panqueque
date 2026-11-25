import ConPanqueque.Front.ScanPhase
import ConPanqueque.Front.KBCall

/-! # The scan phase in one scan

`lineFunKB` scans the line once (`lineStmt`), leaves the payload tag, the payload's value/position and the
index in the key buffer, and returns the next position.  `specR_scanPhaseK` replaces the four `lineFun`
calls of `specR_scanPhase` (each scanning the line again) by one call and three loads, with the same
`ScanOut` for the continuation. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (LineRec LinePayload ScanRes scanLineFwd)

variable {σ : Type}

def fLnKB := ofString "lnkb"

/-- `KB[k] := e`. -/
def kbStore (k : Nat) (e : ExpHOL 64) : ProgHOL 64 :=
  .store (.op .add [.var .global gKb, .const (BitVec.ofNat 64 (8 * k))]) e

/-- `lnkb(b, n, i)`: scan the line at `i`; `KB := [tag, value/position, index]`; return the next position. -/
def lineFunKB : ProgHOL 64 :=
  decsOf lineFunLocals (.seq lineStmt (.seq (kbStore 0 (vv sPl)) (.seq (kbStore 1 (vv (slotName 0)))
    (.seq (kbStore 2 (vv sIdx)) (.return (vv sI))))))

theorem eval_kbAddr (u : PanSemStateFiniteExact 64 σ) (KB : BitVec 64) (k : Nat)
    (hKB : u.globals.lookup gKb = some (.val (.word KB))) :
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
      (.op .add [.var .global gKb, .const (BitVec.ofNat 64 (8 * k))]) =
      some (.val (.word (KB + BitVec.ofNat 64 (8 * k)))) := by
  rw [evalHOLExact]
  simp [evalListHOLExact, evalHOLExact, hKB, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem foldl_setVar_memory (ds : List (MlS × BitVec 64)) :
    ∀ t : PanSemStateFiniteExact 64 σ,
      (ds.foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t).memory = t.memory := by
  induction ds with
  | nil => intro t; rfl
  | cons d r ih => intro t; obtain ⟨x, w⟩ := d; exact ih _

theorem lineFunKB_spec (t : PanSemStateFiniteExact 64 σ) (A KB : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc : LineCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (hKB : t.globals.lookup gKb = some (.val (.word KB)))
    (hdom : ∀ j, j < 3 → t.memaddrs (KB + BitVec.ofNat 64 (8 * j)))
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetK KB t lineFunKB (fun wn wt ws wi => ∃ u' : PanSemStateFiniteExact 64 σ, LineOut b i u' ∧
      u'.locals.lookup sI = some (.val (.word wn)) ∧ u'.locals.lookup sPl = some (.val (.word wt)) ∧
      u'.locals.lookup (slotName 0) = some (.val (.word ws)) ∧ u'.locals.lookup sIdx = some (.val (.word wi))) := by
  unfold lineFunKB
  apply retK_decsOf
  have hlk := fun y => lookup_foldl_setVar (σ := σ) y lineFunLocals t
  let u0 := lineFunLocals.foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t
  have L : ∀ y, u0.locals.lookup y = _ := hlk
  have e := lineStmt_spec t A b hp hb hc i hi u0 rfl rfl rfl rfl rfl
    (by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK, sIdx,
      sPl, sC, sK, sV, sKK, sE2]; exact lb)
    (by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK, sIdx,
      sPl, sC, sK, sV, sKK, sE2]; exact ln)
    (by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK, sIdx,
      sPl, sC, sK, sV, sKK, sE2]; exact li)
    (by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK, sIdx,
      sPl, sC, sK, sV, sKK, sE2])
    (by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK, sIdx,
      sPl, sC, sK, sV, sKK, sE2])
    (by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK, sIdx,
      sPl, sC, sK, sV, sKK, sE2])
    (by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK, sIdx,
      sPl, sC, sK, sV, sKK, sE2])
    (by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK, sIdx,
      sPl, sC, sK, sV, sKK, sE2])
    ⟨0, by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG, sW, sIK,
      sIdx, sPl, sC, sK, sV, sKK, sE2]⟩
    (by intro y hy; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨0, by rw [L]; simp (config := {decide := true}) [lineFunLocals, slotName, slotNames, sB, sN, sI, sG,
            sW, sIK, sIdx, sPl, sC, sK, sV, sKK, sE2]⟩)
  rcases e with hs | ⟨hn, hout, f1, f2, f3, f4, f5⟩
  · exact Or.inl (seq_stop u0 _ _ hs)
  generalize he : evaluateHOLFiniteState u0 lineStmt = r at hn hout f1 f2 f3 f4 f5
  obtain ⟨r1, u1⟩ := r
  simp only at hn hout f1 f2 f3 f4 f5
  subst hn
  -- the four words the scan leaves
  obtain ⟨rec, next, hsc, hli, hk⟩ := id hout
  have hw : ∃ wt ws wi, u1.locals.lookup sPl = some (.val (.word wt)) ∧
      u1.locals.lookup (slotName 0) = some (.val (.word ws)) ∧ u1.locals.lookup sIdx = some (.val (.word wi)) := by
    rcases hk with ⟨-, hpl, hrest⟩ | ⟨ik, idx, pl, wpl, ws0, j0, j', lik, lidx, lpl, ls0, -⟩
    · obtain ⟨ws, hws⟩ := hrest (slotName 0) (by simp)
      obtain ⟨wi, hwi⟩ := hrest sIdx (by simp)
      exact ⟨0, ws, wi, hpl, hws, hwi⟩
    · exact ⟨wpl, ws0, _, lpl, ls0, lidx⟩
  obtain ⟨wt, ws, wi, lt, ls, lix⟩ := hw
  unfold RetK
  rw [seq_normal _ he]
  simp only [kbStore]
  have hKB1 : u1.globals.lookup gKb = some (.val (.word KB)) := by rw [f3]; exact hKB
  have hd1 : ∀ j, j < 3 → u1.memaddrs (KB + BitVec.ofNat 64 (8 * j)) := fun j hj => by rw [f2]; exact hdom j hj
  rw [seq_normal _ (store_word u1 _ _ _ wt (eval_kbAddr u1 KB 0 hKB1) (eval_vv u1 sPl _ lt) (hd1 0 (by decide)))]
  let u2 : PanSemStateFiniteExact 64 σ :=
    { u1 with memory := fun c => if c = KB + BitVec.ofNat 64 (8 * 0) then .word wt else u1.memory c }
  rw [seq_normal _ (store_word u2 _ _ _ ws (eval_kbAddr u2 KB 1 hKB1) (eval_vv u2 (slotName 0) _ ls) (hd1 1 (by decide)))]
  let u3 : PanSemStateFiniteExact 64 σ :=
    { u2 with memory := fun c => if c = KB + BitVec.ofNat 64 (8 * 1) then .word ws else u2.memory c }
  rw [seq_normal _ (store_word u3 _ _ _ wi (eval_kbAddr u3 KB 2 hKB1) (eval_vv u3 sIdx _ lix) (hd1 2 (by decide)))]
  let u4 : PanSemStateFiniteExact 64 σ :=
    { u3 with memory := fun c => if c = KB + BitVec.ofNat 64 (8 * 2) then .word wi else u3.memory c }
  have hn4 : u4.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 next.toNat))) := hli
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv u4 sI _ hn4
  refine Or.inr ⟨_, wt, ws, wi, q1, ⟨u1, hout, hli, lt, ls, lix⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [q2]; show u4.memory = _
    funext c; simp only [u4, u3, u2, kbSt]; rw [f1, foldl_setVar_memory]
  · rw [q3]; exact f2
  · rw [q4]; exact f3
  · rw [q5]; exact f4
  · rw [q6]; exact f5

/-- **The scan phase in one scan.** -/
theorem specR_scanPhaseK {α : Type} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64}
    (C : Ctx) (hok : CtxOK C) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b)
    (hlc : ∀ t : PState σ, t.code = C.code → LineCodes t)
    (hc : C.code.lookup fLnKB = some ([(sB, .one), (sN, .one), (sI, .one)], lineFunKB, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kTg, kS0, kIx, kNx], x ∈ D)
    (i : USize) (hi : i.toNat ≤ b.size) (rec : LineRec) (next : USize) (hs : scanLineFwd b i = .ok rec next)
    (hLI : Γ.get kLI = some (BitVec.ofNat 64 i.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hk : ∀ wt ws wi wn, ScanOut b rec next wt ws wi wn →
      SpecR (Inv C s ((kIx, wi) :: (kS0, ws) :: (kTg, wt) :: (kNx, wn) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D)
      (.seq (callTo kNx fLnKB [vv kBA, vv kBN, vv kLI]) (.seq (.assign .local kTg (kbLoad 0))
        (.seq (.assign .local kS0 (kbLoad 1)) (.seq (.assign .local kIx (kbLoad 2)) rest)))) s m R := by
  have hplat := hbuf.plat
  refine specR_callK3 hok kNx kTg kS0 kIx fLnKB sB sN sI lineFunKB (vv kBA) (vv kBN) (vv kLI) (cellA C bufJ)
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 i.toNat) _ (by decide) (by decide) (by decide)
    (hD _ (by simp)) (hD _ (by simp)) (hD _ (by simp)) (hD _ (by simp)) hc
    (by simpa [sev, vv] using hBA) (by simpa [sev, vv] using hBN) (by simpa [sev, vv] using hLI)
    (fun t callee ht c1 c2 c3 => lineFunKB_spec (callEntryStateHOLFinite t callee) (cellA C bufJ) C.KB b hplat
      (bytesAt_congr (t := t) (bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk
        (Nat.le_refl _)) rfl rfl rfl)
      (hlc _ (by show t.code = C.code; exact ht.sr.code)) i hi
      (by show t.globals.lookup gKb = _; exact ht.sr.gkb) (fun j hj => ht.sr.kbuf j hj) c1 c2 c3)
    (fun wn wt ws wi ⟨u', ho, hn', hpl', hs0', hix'⟩ => hk wt ws wi wn ⟨?_, ?_, fun hnb => ?_⟩)
  · rcases (lineOut_rec hs ho).2 with ⟨hb, hp⟩ | ⟨hnb, ik, idx, wpl, ws0, j0, j', -, hp, -, hpl, -⟩
    · subst hb; exact (lk_word hpl' hp)
    · rw [lk_word hpl' hp]; exact plOK_tag_eq hpl
  · exact (lk_word hn' (lineOut_rec hs ho).1)
  · rcases (lineOut_rec hs ho).2 with ⟨hb, -⟩ | ⟨-, ik, idx, wpl, ws0, j0, j', hi3, hp, hs2, hpl, hle⟩
    · exact absurd hb hnb
    refine ⟨?_, j0, ik, idx, j', hle, lk_word hix' hi3⟩
    rw [lk_word hs0' hs2, lk_word hpl' hp]; exact hpl

end ConPanqueque.Front
