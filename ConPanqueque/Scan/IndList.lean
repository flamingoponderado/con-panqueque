import ConPanqueque.Scan.NatNth
import ConPanqueque.Scan.ObjFun
import ConPanqueque.Scan.IndSpec
import ConPanqueque.Scan.RecFuns

/-! # A list of records, in Pancake

`olCore item ret` walks the `[ … ]` at `i` as con-leche's `scan*ListLoop` does (whitespace, a `{`
item read by the Pancake function `item`, a comma, the closing bracket), counting the items (`m`)
and keeping the position of item number `l` (`res`).  It returns `ret`: the list's end (`sI`), the
number of items (`sM`) or the position of item `l` (`sR`).

`olCore_sound`: when it returns, con-leche's list scanner (`objListOpen sc`, with `sc` the item's
Lean model, see `ItemSound`) accepts the list at `i` as `xs`, ending at `e`, and the word is `e`,
`xs.length`, or (when `l < xs.length`) a position `q` where `sc` reads `xs[l]`.  The count is exact:
`xs.length ≤ e ≤ b.size + 64`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

/-! ## con-leche's side -/

theorem objList_unfold {α : Type} (item : ByteArray → USize → ScanRes α) (b : ByteArray) {j : USize}
    (h : j < b.usize) (acc : List α) (w : Bool) :
    objList item b j acc w =
      if isWs (byteAt b j) then objList item b (j + 1) acc w
      else if byteAt b j == 93 then
        (if w && !acc.isEmpty then .err ⟨j.toNat, .expectedList⟩ else .ok acc.reverse (j + 1))
      else if byteAt b j == 44 then
        (if w then .err ⟨j.toNat, .expectedList⟩ else objList item b (j + 1) acc true)
      else if byteAt b j == 123 then
        (if !w then .err ⟨j.toNat, .expectedList⟩ else
          match item b j with
          | .err err => .err err
          | .ok x e => if _hj : j < e then objList item b e (x :: acc) false else .err ⟨j.toNat, .noProgress⟩)
      else .err ⟨j.toNat, .expectedList⟩ := by
  rw [objList, dite_eq_left h, byteAt_uget h]
  rfl

theorem objList_len {α : Type} (item : ByteArray → USize → ScanRes α) (b : ByteArray) :
    ∀ msr (i : USize) (acc : List α) (wi : Bool), b.size - i.toNat = msr →
      ∀ xs e, objList item b i acc wi = .ok xs e → xs.length ≤ acc.length + (b.size - i.toNat) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | ind msr ih =>
    intro i acc wi hm xs e h
    rw [objList] at h
    split at h
    · rename_i hi
      have h1 := usizeInBounds b i hi
      have h2 := usizeStep b i hi
      simp only at h
      split at h
      · have := ih _ (by omega) _ _ _ rfl _ _ h; omega
      split at h
      · split at h
        · simp at h
        · simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, -⟩ := h; simp
      split at h
      · split at h
        · simp at h
        · have := ih _ (by omega) _ _ _ rfl _ _ h; omega
      split at h
      · split at h
        · simp at h
        split at h
        · simp at h
        split at h
        · rename_i hj
          have hj' := USize.lt_iff_toNat_lt.mp hj
          have := ih _ (by omega) _ _ _ rfl _ _ h
          simp only [List.length_cons] at this
          omega
        · simp at h
      · simp at h
    · simp at h

/-- **A list's length is bounded by the buffer size.** -/
theorem objListOpen_len {α : Type} {item : ByteArray → USize → ScanRes α} {b : ByteArray} {v e : USize}
    {xs : List α} (h : objListOpen item b v = .ok xs e) : xs.length ≤ b.size := by
  rw [objListOpen] at h
  split at h
  · have := objList_len item b _ _ [] true rfl _ _ h; simp at this; omega
  · simp at h

/-! ## The Pancake function -/

/-- One `{`-item: call `item`, keep the position when it is item number `l`, count it, step past it. -/
def olItem (item : MlS) : ProgHOL 64 :=
  .seq (callTo sE2 item [vv sB, vv sN, vv sI])
    (.ite (.cmp .lower (vv sI) (vv sE2))
      (.seq (.ite (.cmp .equal (vv sM) (vv sL)) (.assign .local sR (vv sI)) .skip)
        (.seq (.assign .local sM (.op .add [vv sM, .const 1]))
          (.seq (.assign .local sW (.const 0)) (.assign .local sI (vv sE2)))))
      hang)

def olBody (item : MlS) : ProgHOL 64 :=
  .seq (bAt sC (vv sI))
    (.ite wsTest incI
      (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 93)))
        (.ite (.op .and [vv sW, .cmp .notEqual (vv sM) (.const 0)]) hang
          (.seq incI (.assign .local sG (.const 0))))
        (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 44)))
          (.ite (vv sW) hang (.seq (.assign .local sW (.const 1)) incI))
          (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 123)))
            (.ite (vv sW) (olItem item) hang)
            hang))))

/-- The list at `i`: the opening bracket, the loop, then `ret`. -/
def olCore (item ret : MlS) : ProgHOL 64 :=
  .seq (bAt sC (vv sI))
    (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 91)))
      (.seq incI (.seq (.while (vv sG) (olBody item)) (.return (vv ret))))
      hang)

/-- The list function's own locals. -/
def olLocals : List (MlS × BitVec 64) := [(sC, 0), (sE2, 0), (sG, 1), (sW, 1), (sM, 0), (sR, 0)]

/-- `list(b, n, i)`: three parameters (item number `0` for `sR`). -/
def olFun3 (item ret : MlS) : ProgHOL 64 := decsOf ((sL, 0) :: olLocals) (olCore item ret)

/-- `list(b, n, i, l)`. -/
def olFun4 (item ret : MlS) : ProgHOL 64 := decsOf olLocals (olCore item ret)

section
variable {σ : Type}

/-- A record function: `fn` is in the code table, and from any state with that table it returns an
end `e` where `sc` accepts the record. -/
def ItemSound {α : Type} (t : PanSemStateFiniteExact 64 σ) (fn : MlS) (sc : ByteArray → USize → ScanRes α) : Prop :=
  ∃ body, t.code.lookup fn = some ([(sB, .one), (sN, .one), (sI, .one)], body, .one) ∧
    ∀ (s : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray), s.code = t.code → Plat b →
      BytesAt s A b.data.toList → ∀ (v : USize), v.toNat ≤ b.size →
      s.locals.lookup sB = some (.val (.word A)) →
      s.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      s.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))) →
      RetP s body (fun w => ∃ (e : USize), w = BitVec.ofNat 64 e.toNat ∧ e.toNat ≤ b.size + 64 ∧
        ∃ x, sc b v = .ok x e)

theorem ItemSound.congr {α : Type} {t u : PanSemStateFiniteExact 64 σ} {fn : MlS}
    {sc : ByteArray → USize → ScanRes α} (h : ItemSound t fn sc) (hc : u.code = t.code) : ItemSound u fn sc := by
  obtain ⟨body, hl, hs⟩ := h
  exact ⟨body, by rw [hc]; exact hl, fun s A b hsc => hs s A b (hsc.trans hc)⟩

theorem ok_call3P {s : PanSemStateFiniteExact 64 σ} {x f x1 x2 x3 : MlS} {body q : ProgHOL 64}
    {a1 a2 a3 : ExpHOL 64} {v1 v2 v3 w0 : BitVec 64} {P : BitVec 64 → Prop} {Q : PanSemStateFiniteExact 64 σ → Prop}
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (ha1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a1 =
      some (.val (.word v1)))
    (ha2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a2 =
      some (.val (.word v2)))
    (ha3 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a3 =
      some (.val (.word v3)))
    (hx : s.locals.lookup x = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetP (callEntryStateHOLFinite s callee) body P)
    (k : ∀ w u, P w → SetsLocal s x w u → Ok u q Q) : Ok s (.seq (callTo x f [a1, a2, a3]) q) Q := by
  rcases call3_retP s x f x1 x2 x3 body a1 a2 a3 v1 v2 v3 w0 P h12 h13 h23 hcode ha1 ha2 ha3 hx hbody with
    hs | ⟨w, u, hp, hu, m, d, g, c, b, lx, lo⟩
  · exact Or.inl (seq_stop s _ _ hs)
  · exact ok_seq hu (k w u hp ⟨m, d, g, c, b, lx, lo⟩)

theorem ok_skip (u : PanSemStateFiniteExact 64 σ) {Q : PanSemStateFiniteExact 64 σ → Prop} (h : Q u) :
    Ok u .skip Q := by
  unfold Ok; rw [skip_eval]; exact Or.inr ⟨rfl, h⟩

/-- The loop invariant: at `j`, wanting an item or not, with `acc` read (reversed), the count in `m`,
item number `J`'s position in `res` once read; then con-leche's loop from there gives `R`, or the
loop is done with `R` its answer. -/
def OlI {α : Type} (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (sc : ByteArray → USize → ScanRes α) (J : Nat) (R : ScanRes (List α)) (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧ u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) ∧
  u.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J))) ∧
  (∃ w, u.locals.lookup sC = some (.val (.word w))) ∧ (∃ w, u.locals.lookup sE2 = some (.val (.word w))) ∧
  ∃ (j : USize) (wm : Bool) (acc : List α) (wr : BitVec 64), j.toNat ≤ b.size + 64 ∧ acc.length ≤ j.toNat ∧
    u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) ∧
    u.locals.lookup sW = some (.val (.word (bw (wm = true)))) ∧
    u.locals.lookup sM = some (.val (.word (BitVec.ofNat 64 acc.length))) ∧
    u.locals.lookup sR = some (.val (.word wr)) ∧
    (J < acc.length → ∃ (q e : USize) (x : α), wr = BitVec.ofNat 64 q.toNat ∧ acc.reverse[J]? = some x ∧
      sc b q = .ok x e) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ objList sc b j acc wm = R) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ R = .ok acc.reverse j))

theorem bw_true_ne {p : Prop} [Decidable p] (h : bw p ≠ 0) : p := by
  by_cases hp : p
  · exact hp
  · simp [bw, hp] at h

theorem bw_false_eq {p : Prop} [Decidable p] (h : bw p = 0) : ¬ p := by
  intro hp; simp [bw, hp] at h

theorem ol_step {α : Type} (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (item : MlS) (sc : ByteArray → USize → ScanRes α) (hit : ItemSound t item sc)
    (J : Nat) (hJ : J < 2 ^ 64) (R : ScanRes (List α))
    (u : PanSemStateFiniteExact 64 σ) (hu : OlI t A b sc J R u) (hg : u.locals.lookup sG = some (.val (.word 1))) :
    Ok (decClockHOLFinite u) (olBody item) (OlI t A b sc J R) := by
  obtain ⟨m0, d0, c0, g0, b0, lb, ln, ll, ⟨wc, lc⟩, ⟨we, le⟩, j, wm, acc, wr, hj, hacc, li, lw, lm, lr, hpos, br⟩ := hu
  obtain ⟨_, hR⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  let v := decClockHOLFinite u
  have hbv : BytesAt v A b.data.toList := bytesAt_congr hb m0 d0 b0
  unfold olBody
  have e1 := bAt_spec v A b.data.toList sC (vv sI) j.toNat hbv (by omega) wc (by lk [v]; exact lc)
    (by lk [v]; exact lb) (by lk [v]; simpa using ln) (eval_vv v sI _ (by lk [v]; exact li))
  refine ok_seq e1 ?_
  generalize hcd : byteL b.data.toList j.toNat = c at e1
  let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 c.toNat))) v
  have L1 : ∀ y, y ≠ sC → v1.locals.lookup y = u.locals.lookup y := fun y h => by
    simp only [v1, v]; rw [lookup_setVar_other _ _ h]; rfl
  have lc1 : v1.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 c.toNat))) := by lk [v1]
  have hct : c.toNat < 256 := UInt8.toNat_lt c
  have hfr : ∀ (w : PanSemStateFiniteExact 64 σ), w.memory = v1.memory → w.memaddrs = v1.memaddrs →
      w.code = v1.code → w.globals = v1.globals → w.be = v1.be →
      w.memory = t.memory ∧ w.memaddrs = t.memaddrs ∧ w.code = t.code ∧ w.globals = t.globals ∧ w.be = t.be :=
    fun w a1 a2 a3 a4 a5 => ⟨a1.trans m0, a2.trans d0, a3.trans c0, a4.trans g0, a5.trans b0⟩
  -- an in-range byte
  have inb : c.toNat ≠ 0 → j.toNat < b.size ∧ j < b.usize ∧ byteAt b j = c := by
    intro h0
    have hjl : j.toNat < b.size := by
      have := lt_of_byteL (bs := b.data.toList) (p := j.toNat) (c := c.toNat) (by rw [hcd]) h0; simpa using this
    refine ⟨hjl, (hp.lt_iff j).mpr hjl, ?_⟩
    rw [byteAt_eq hp j, ← hcd]; rfl
  have hj1 : ∀ (h : j < b.usize), (j + 1).toNat = j.toNat + 1 := fun h => usizeStep b j h
  refine ok_ite (wsTest_ok v1 c.toNat hct lc1) (fun hw => ?_) (fun hw => ?_)
  · -- whitespace
    have hws : isWsN c.toNat = true := bw_true_ne hw
    have h0 : c.toNat ≠ 0 := by intro h; rw [h] at hws; simp [isWsN] at hws
    obtain ⟨hjl, hju, hbc⟩ := inb h0
    rw [objList_unfold sc b hju, hbc, isWs_eq, hws, if_pos rfl] at hR
    have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      rw [L1 _ (by decide)]; exact li
    refine ok_assign (v := BitVec.ofNat 64 (j + 1).toNat) (by
      rw [eval_add_c v1 sI _ _ li1, hj1 hju]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li1 ?_
    have L2 : ∀ y, y ≠ sI → y ≠ sC →
        (setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j + 1).toNat))) v1).locals.lookup y = u.locals.lookup y :=
      fun y h h' => by rw [lookup_setVar_other _ _ h, L1 y h']
    obtain ⟨m', d', c', g', b'⟩ := hfr _ rfl rfl rfl rfl rfl
    refine ⟨m', d', c', g', b', by rw [L2 _ (by decide) (by decide)]; exact lb,
      by rw [L2 _ (by decide) (by decide)]; exact ln, by rw [L2 _ (by decide) (by decide)]; exact ll,
      ⟨_, by rw [lookup_setVar_other _ _ (by decide)]; exact lc1⟩, ⟨we, by rw [L2 _ (by decide) (by decide)]; exact le⟩,
      j + 1, wm, acc, wr, by rw [hj1 hju]; omega, by rw [hj1 hju]; omega, by lk, by rw [L2 _ (by decide) (by decide)]; exact lw,
      by rw [L2 _ (by decide) (by decide)]; exact lm, by rw [L2 _ (by decide) (by decide)]; exact lr, hpos,
      Or.inl ⟨by rw [L2 _ (by decide) (by decide)]; exact hg, hR⟩⟩
  have hnws : isWsN c.toNat = false := by
    have := bw_false_eq hw; simpa using this
  refine ok_ite (eval_eq_c v1 sC c.toNat 93 (by omega) (by decide) lc1) (fun hw93 => ?_) (fun hw93 => ?_)
  · -- `]`
    have h93 : c.toNat = 93 := bw_true_ne hw93
    obtain ⟨hjl, hju, hbc⟩ := inb (by omega)
    have hc93 : (c == 93) = true := by
      rw [show (93 : UInt8) = UInt8.ofNat 93 from rfl, beq_ofNat c 93 (by decide)]; simp [h93]
    rw [objList_unfold sc b hju, hbc, isWs_eq, hnws, hc93] at hR
    simp only [Bool.false_eq_true, ↓reduceIte] at hR
    have lw1 : v1.locals.lookup sW = some (.val (.word (bw (wm = true)))) := by rw [L1 _ (by decide)]; exact lw
    have lm1 : v1.locals.lookup sM = some (.val (.word (BitVec.ofNat 64 acc.length))) := by
      rw [L1 _ (by decide)]; exact lm
    have hm0 : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.cmp .notEqual (vv sM) (.const 0)) = some (.val (.word (bw (acc.length ≠ 0)))) := by
      rw [ConsLoop.eval_cmp_of v1 .notEqual _ _ _ (BitVec.ofNat 64 0) (eval_vv v1 sM _ lm1) (by simp [evalHOLExact])]
      have hlt : acc.length < 2 ^ 64 := by omega
      by_cases h0 : acc.length = 0
      · have e0 : (BitVec.ofNat 64 acc.length == BitVec.ofNat 64 0) = true := by rw [h0]; rfl
        simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bw,
          h0, ne_eq, not_true_eq_false]; rfl
      · have e0 : (BitVec.ofNat 64 acc.length == BitVec.ofNat 64 0) = false :=
          beq_eq_false_iff_ne.mpr (fun e => h0 ((ofNat_inj _ 0 hlt (by decide)).mp e))
        simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e0, Bool.not_false, ↓reduceIte, bw, h0, ne_eq,
          not_false_eq_true]
    have hand : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.op .and [vv sW, .cmp .notEqual (vv sM) (.const 0)]) = some (.val (.word (bw (wm = true ∧ acc.length ≠ 0)))) := by
      rw [evalHOLExact]; simp only [evalListHOLExact, eval_vv v1 sW _ lw1, hm0]
      simp [valueIsWord, valueWord, bw_and]
    refine ok_ite hand (fun _ => ok_hang _ _) (fun hw0 => ?_)
    have hbad := bw_false_eq hw0
    have hok : (wm && !acc.isEmpty) = false := by
      cases wm
      · rfl
      · cases acc with
        | nil => rfl
        | cons _ _ => simp at hbad
    rw [hok] at hR; simp only [Bool.false_eq_true, ↓reduceIte] at hR
    have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      rw [L1 _ (by decide)]; exact li
    unfold incI
    refine ok_seq (ConsLoop.assign_local v1 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
      rw [eval_add_c v1 sI _ _ li1, hj1 hju]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li1) ?_
    let v2 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j + 1).toNat))) v1
    refine ok_assign (v := 0) (by simp [evalHOLExact]) (by lk [v2]; rw [L1 _ (by decide)]; exact hg) ?_
    have L2 : ∀ y, y ≠ sG → y ≠ sI → y ≠ sC →
        (setVarHOLFinite sG (.val (.word 0)) v2).locals.lookup y = u.locals.lookup y :=
      fun y h h' h'' => by rw [lookup_setVar_other _ _ h, lookup_setVar_other _ _ h', L1 y h'']
    obtain ⟨m', d', c', g', b'⟩ := hfr _ rfl rfl rfl rfl rfl
    refine ⟨m', d', c', g', b', by rw [L2 _ (by decide) (by decide) (by decide)]; exact lb,
      by rw [L2 _ (by decide) (by decide) (by decide)]; exact ln, by rw [L2 _ (by decide) (by decide) (by decide)]; exact ll,
      ⟨_, by lk [v2]; exact lc1⟩, ⟨we, by rw [L2 _ (by decide) (by decide) (by decide)]; exact le⟩,
      j + 1, wm, acc, wr, by rw [hj1 hju]; omega, by rw [hj1 hju]; omega, by lk [v2],
      by rw [L2 _ (by decide) (by decide) (by decide)]; exact lw,
      by rw [L2 _ (by decide) (by decide) (by decide)]; exact lm, by rw [L2 _ (by decide) (by decide) (by decide)]; exact lr,
      hpos, Or.inr ⟨by lk, hR.symm⟩⟩
  have hn93 : c.toNat ≠ 93 := bw_false_eq hw93
  have hc93 : (c == 93) = false := by
    rw [show (93 : UInt8) = UInt8.ofNat 93 from rfl, beq_ofNat c 93 (by decide)]; simp [hn93]
  refine ok_ite (eval_eq_c v1 sC c.toNat 44 (by omega) (by decide) lc1) (fun hw44 => ?_) (fun hw44 => ?_)
  · -- `,`
    have h44 : c.toNat = 44 := bw_true_ne hw44
    obtain ⟨hjl, hju, hbc⟩ := inb (by omega)
    have hc44 : (c == 44) = true := by
      rw [show (44 : UInt8) = UInt8.ofNat 44 from rfl, beq_ofNat c 44 (by decide)]; simp [h44]
    rw [objList_unfold sc b hju, hbc, isWs_eq, hnws, hc93, hc44] at hR
    simp only [Bool.false_eq_true, ↓reduceIte] at hR
    have lw1 : v1.locals.lookup sW = some (.val (.word (bw (wm = true)))) := by rw [L1 _ (by decide)]; exact lw
    refine ok_ite (eval_vv v1 sW _ lw1) (fun _ => ok_hang _ _) (fun hw0 => ?_)
    have hwm : wm = false := by have := bw_false_eq hw0; simpa using this
    subst hwm
    simp only [Bool.false_eq_true, ↓reduceIte] at hR
    refine ok_seq (ConsLoop.assign_local v1 sW (.const 1) 1 _ (by simp [evalHOLExact]) lw1) ?_
    let v2 := setVarHOLFinite sW (.val (.word 1)) v1
    have li2 : v2.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      lk [v2]; rw [L1 _ (by decide)]; exact li
    refine ok_assign (v := BitVec.ofNat 64 (j + 1).toNat) (by
      rw [eval_add_c v2 sI _ _ li2, hj1 hju]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li2 ?_
    have L2 : ∀ y, y ≠ sI → y ≠ sW → y ≠ sC →
        (setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j + 1).toNat))) v2).locals.lookup y = u.locals.lookup y :=
      fun y h h' h'' => by rw [lookup_setVar_other _ _ h, lookup_setVar_other _ _ h', L1 y h'']
    obtain ⟨m', d', c', g', b'⟩ := hfr _ rfl rfl rfl rfl rfl
    refine ⟨m', d', c', g', b', by rw [L2 _ (by decide) (by decide) (by decide)]; exact lb,
      by rw [L2 _ (by decide) (by decide) (by decide)]; exact ln, by rw [L2 _ (by decide) (by decide) (by decide)]; exact ll,
      ⟨_, by lk [v2]; exact lc1⟩, ⟨we, by rw [L2 _ (by decide) (by decide) (by decide)]; exact le⟩,
      j + 1, true, acc, wr, by rw [hj1 hju]; omega, by rw [hj1 hju]; omega, by lk, by lk [v2]; rfl,
      by rw [L2 _ (by decide) (by decide) (by decide)]; exact lm, by rw [L2 _ (by decide) (by decide) (by decide)]; exact lr,
      hpos, Or.inl ⟨by rw [L2 _ (by decide) (by decide) (by decide)]; exact hg, hR⟩⟩
  have hn44 : c.toNat ≠ 44 := bw_false_eq hw44
  have hc44 : (c == 44) = false := by
    rw [show (44 : UInt8) = UInt8.ofNat 44 from rfl, beq_ofNat c 44 (by decide)]; simp [hn44]
  refine ok_ite (eval_eq_c v1 sC c.toNat 123 (by omega) (by decide) lc1) (fun hw123 => ?_) (fun _ => ok_hang _ _)
  -- `{`: an item
  have h123 : c.toNat = 123 := bw_true_ne hw123
  obtain ⟨hjl, hju, hbc⟩ := inb (by omega)
  have hc123 : (c == 123) = true := by
    rw [show (123 : UInt8) = UInt8.ofNat 123 from rfl, beq_ofNat c 123 (by decide)]; simp [h123]
  rw [objList_unfold sc b hju, hbc, isWs_eq, hnws, hc93, hc44, hc123] at hR
  simp only [Bool.false_eq_true, ↓reduceIte] at hR
  have lw1 : v1.locals.lookup sW = some (.val (.word (bw (wm = true)))) := by rw [L1 _ (by decide)]; exact lw
  refine ok_ite (eval_vv v1 sW _ lw1) (fun hw1 => ?_) (fun _ => ok_hang _ _)
  have hwm : wm = true := by have := bw_true_ne hw1; simpa using this
  subst hwm
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hR
  obtain ⟨body, hcode, hsound⟩ := hit
  have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [L1 _ (by decide)]; exact li
  unfold olItem
  refine ok_call3P (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 j.toNat) (w0 := we)
    (by decide) (by decide) (by decide) (by rw [show v1.code = t.code from c0]; exact hcode)
    (eval_vv v1 sB _ (by rw [L1 _ (by decide)]; exact lb)) (eval_vv v1 sN _ (by rw [L1 _ (by decide)]; exact ln))
    (eval_vv v1 sI _ li1) (by rw [L1 _ (by decide)]; exact le)
    (fun callee h1 h2 h3 => hsound (callEntryStateHOLFinite v1 callee) A b
      (by simp only [callEntryStateHOLFinite]; exact c0) hp (bytesAt_congr hbv rfl rfl rfl) j (by omega) h1 h2 h3)
    (fun w u1 hP hs1 => ?_)
  obtain ⟨E, rfl, hEl, x, hx⟩ := hP
  obtain ⟨m1, d1, g1, c1, b1, le1, lo1⟩ := hs1
  rw [hx] at hR
  simp only at hR
  have L2 : ∀ y, y ≠ sE2 → y ≠ sC → u1.locals.lookup y = u.locals.lookup y := fun y h h' => by
    rw [lo1 y h, L1 y h']
  refine ok_ite (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1 sI _ (by rw [L2 _ (by decide) (by decide)]; exact li)) (eval_vv u1 sE2 _ le1))
    (fun hwE => ?_) (fun _ => ok_hang _ _)
  have hjE : j.toNat < E.toNat := bw_true_ne hwE
  rw [dite_eq_left (USize.lt_iff_toNat_lt.mpr hjE)] at hR
  have lm1 : u1.locals.lookup sM = some (.val (.word (BitVec.ofNat 64 acc.length))) := by
    rw [L2 _ (by decide) (by decide)]; exact lm
  have ll1 : u1.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J))) := by
    rw [L2 _ (by decide) (by decide)]; exact ll
  have lr1 : u1.locals.lookup sR = some (.val (.word wr)) := by rw [L2 _ (by decide) (by decide)]; exact lr
  have li1' : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [L2 _ (by decide) (by decide)]; exact li
  have hcmp : @evalHOLExact 64 σ _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
      (.cmp .equal (vv sM) (vv sL)) = some (.val (.word (bw (acc.length = J)))) := by
    rw [ConsLoop.eval_cmp_of u1 .equal _ _ _ _ (eval_vv u1 sM _ lm1) (eval_vv u1 sL _ ll1),
      bw_eq _ _ (by omega) hJ]
  -- after the position update: `res` is `wr'`
  have rest : ∀ (u2 : PanSemStateFiniteExact 64 σ) (wr' : BitVec 64),
      u2.memory = u1.memory → u2.memaddrs = u1.memaddrs → u2.code = u1.code → u2.globals = u1.globals →
      u2.be = u1.be → (∀ y, y ≠ sR → u2.locals.lookup y = u1.locals.lookup y) →
      u2.locals.lookup sR = some (.val (.word wr')) →
      (J < acc.length + 1 → ∃ (q e : USize) (x' : α), wr' = BitVec.ofNat 64 q.toNat ∧
        (x :: acc).reverse[J]? = some x' ∧ sc b q = .ok x' e) →
      Ok u2 (.seq (.assign .local sM (.op .add [vv sM, .const 1]))
          (.seq (.assign .local sW (.const 0)) (.assign .local sI (vv sE2)))) (OlI t A b sc J R) := by
    intro u2 wr' a1 a2 a3 a4 a5 hlo lr2 hpos'
    have lm2 : u2.locals.lookup sM = some (.val (.word (BitVec.ofNat 64 acc.length))) := by
      rw [hlo _ (by decide)]; exact lm1
    refine ok_seq (ConsLoop.assign_local u2 sM _ (BitVec.ofNat 64 (acc.length + 1)) _ (by
      rw [eval_add_c u2 sM _ _ lm2]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) lm2) ?_
    let u3 := setVarHOLFinite sM (.val (.word (BitVec.ofNat 64 (acc.length + 1)))) u2
    refine ok_seq (ConsLoop.assign_local u3 sW (.const 0) 0 _ (by simp [evalHOLExact])
      (by lk [u3]; rw [hlo _ (by decide), L2 _ (by decide) (by decide)]; exact lw)) ?_
    let u4 := setVarHOLFinite sW (.val (.word 0)) u3
    refine ok_assign (v := BitVec.ofNat 64 E.toNat) (eval_vv u4 sE2 _ (by lk [u4, u3]; rw [hlo _ (by decide)]; exact le1))
      (by lk [u4, u3]; rw [hlo _ (by decide)]; exact li1') ?_
    have L3 : ∀ y, y ≠ sI → y ≠ sW → y ≠ sM → y ≠ sR → y ≠ sE2 → y ≠ sC →
        (setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 E.toNat))) u4).locals.lookup y = u.locals.lookup y :=
      fun y h1 h2 h3 h4 h5 h6 => by
        rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h3, hlo y h4, L2 y h5 h6]
    refine ⟨a1.trans (m1.trans m0), a2.trans (d1.trans d0), a3.trans (c1.trans c0), a4.trans (g1.trans g0),
      a5.trans (b1.trans b0), by rw [L3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lb,
      by rw [L3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ln,
      by rw [L3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ll,
      ⟨_, by lk [u4, u3]; rw [hlo _ (by decide), lo1 _ (by decide)]; exact lc1⟩,
      ⟨_, by lk [u4, u3]; rw [hlo _ (by decide)]; exact le1⟩,
      E, false, x :: acc, wr', hEl, by simp only [List.length_cons]; omega, by lk, by lk [u4]; rfl,
      by lk [u4, u3]; simp, by lk [u4, u3]; exact lr2, hpos',
      Or.inl ⟨by rw [L3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg, hR⟩⟩
  have hrev : ∀ k, k < acc.length → (x :: acc).reverse[k]? = acc.reverse[k]? := by
    intro k hk
    simp only [List.reverse_cons]
    rw [List.getElem?_append_left (by simp; omega)]
  have hlast : (x :: acc).reverse[acc.length]? = some x := by
    simp only [List.reverse_cons]
    rw [List.getElem?_append_right (by simp)]
    simp
  by_cases hJeq : acc.length = J
  · have e2 : evaluateHOLFiniteState u1 (.ite (.cmp .equal (vv sM) (vv sL)) (.assign .local sR (vv sI)) .skip) =
        (none, setVarHOLFinite sR (.val (.word (BitVec.ofNat 64 j.toNat))) u1) := by
      rw [ite_word u1 _ _ _ _ hcmp]
      simp only [bw, hJeq, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact ConsLoop.assign_local u1 sR (vv sI) _ wr (eval_vv u1 sI _ li1') lr1
    refine ok_seq e2 (rest _ (BitVec.ofNat 64 j.toNat) rfl rfl rfl rfl rfl (fun y h => lookup_setVar_other _ _ h)
      (lookup_setVar_same _ _ _) ?_)
    intro _
    exact ⟨j, E, x, rfl, by rw [← hJeq]; exact hlast, hx⟩
  · have e2 : evaluateHOLFiniteState u1 (.ite (.cmp .equal (vv sM) (vv sL)) (.assign .local sR (vv sI)) .skip) =
        (none, u1) := by
      rw [ite_word u1 _ _ _ _ hcmp]
      simp only [bw, hJeq, ↓reduceIte, ne_eq, not_true_eq_false]
      exact skip_eval u1
    refine ok_seq e2 (rest u1 wr rfl rfl rfl rfl rfl (fun _ _ => rfl) lr1 ?_)
    intro hJ'
    have hJa : J < acc.length := by omega
    obtain ⟨q, e', x', hw', hxa, hsc⟩ := hpos hJa
    exact ⟨q, e', x', hw', by rw [hrev J hJa]; exact hxa, hsc⟩

theorem olLoop_spec {α : Type} (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (item : MlS) (sc : ByteArray → USize → ScanRes α) (hit : ItemSound t item sc)
    (J : Nat) (hJ : J < 2 ^ 64) (R : ScanRes (List α))
    (u : PanSemStateFiniteExact 64 σ) (hu : OlI t A b sc J R u) :
    Stop (evaluateHOLFiniteState u (.while (vv sG) (olBody item))).1 ∨
      ((evaluateHOLFiniteState u (.while (vv sG) (olBody item))).1 = none ∧
        OlI t A b sc J R (evaluateHOLFiniteState u (.while (vv sG) (olBody item))).2 ∧
        (evaluateHOLFiniteState u (.while (vv sG) (olBody item))).2.locals.lookup sG = some (.val (.word 0))) := by
  have := while_stop (vv sG) (olBody item) (OlI t A b sc J R)
    (fun u => OlI t A b sc J R u ∧ u.locals.lookup sG = some (.val (.word 0)))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, j, wm, acc, wr, _, _, _, _, _, _, _, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, _⟩
      · exact ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide),
          fun _ _ => ol_step t A b hp hb item sc hit J hJ R u hu hg⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, hg⟩, fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

/-- What a returning list function gives: con-leche's list scanner accepts `xs` ending at `e`, and
the word is `e`, `xs.length`, or the position of item `J`. -/
def OlPost {α : Type} (b : ByteArray) (sc : ByteArray → USize → ScanRes α) (ret : MlS) (v : USize) (J : Nat)
    (w : BitVec 64) : Prop :=
  ∃ (xs : List α) (e : USize), objListOpen sc b v = .ok xs e ∧ e.toNat ≤ b.size + 64 ∧ xs.length ≤ e.toNat ∧
    (ret = sI → w = BitVec.ofNat 64 e.toNat) ∧ (ret = sM → w = BitVec.ofNat 64 xs.length) ∧
    (ret = sR → J < xs.length → ∃ (q e' : USize) (x : α), w = BitVec.ofNat 64 q.toNat ∧ xs[J]? = some x ∧
      sc b q = .ok x e')

theorem olCore_sound {α : Type} (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (item : MlS) (sc : ByteArray → USize → ScanRes α) (hit : ItemSound t item sc)
    (ret : MlS) (hret : ret = sI ∨ ret = sM ∨ ret = sR) (v : USize) (hv : v.toNat ≤ b.size) (J : Nat)
    (hJ : J < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J))))
    (lc : ∃ w, t.locals.lookup sC = some (.val (.word w)))
    (le : ∃ w, t.locals.lookup sE2 = some (.val (.word w)))
    (lg : t.locals.lookup sG = some (.val (.word 1)))
    (lw : t.locals.lookup sW = some (.val (.word 1)))
    (lm : t.locals.lookup sM = some (.val (.word 0)))
    (lr : ∃ w, t.locals.lookup sR = some (.val (.word w))) :
    RetP t (olCore item ret) (OlPost b sc ret v J) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  obtain ⟨wc, lc⟩ := lc
  obtain ⟨we, le⟩ := le
  obtain ⟨wr, lr⟩ := lr
  unfold olCore
  have e1 := bAt_spec t A b.data.toList sC (vv sI) v.toNat hb (by omega) wc lc lb (by simpa using ln)
    (eval_vv t sI _ li)
  refine retP_seq e1 ?_ rfl rfl rfl rfl rfl
  let t1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat))) t
  refine retP_ite (eval_eq_c t1 sC (byteL b.data.toList v.toNat).toNat 91
    (by have := UInt8.toNat_lt (byteL b.data.toList v.toNat); omega) (by decide) (by lk [t1]))
    (fun hw => ?_) (fun _ => retP_hang _ _)
  have hq : (byteL b.data.toList v.toNat).toNat = 91 := bw_true_ne hw
  have hvl : v.toNat < b.size := by have := lt_of_byteL hq (by decide); simpa using this
  have hv1 : (v + 1).toNat = v.toNat + 1 := ConLeche.Frontend.usizeStep b v ((hp.lt_iff v).mpr hvl)
  have hb91 : byteAt b v = 91 := byteAt_of_byteL hp v 91 (by decide) hq
  have hopen : objListOpen sc b v = objList sc b (v + 1) [] true := by
    rw [objListOpen, if_pos (by rw [hb91]; rfl)]
  have li1 : t1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by lk [t1]; exact li
  unfold incI
  refine retP_seq (ConsLoop.assign_local t1 sI _ (BitVec.ofNat 64 (v + 1).toNat) _ (by
    rw [eval_add_c t1 sI _ _ li1, hv1]; congr 3; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]; try omega) li1) ?_ rfl rfl rfl rfl rfl
  let t2 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (v + 1).toNat))) t1
  have h0 : OlI t2 A b sc J (objList sc b (v + 1) [] true) t2 :=
    ⟨rfl, rfl, rfl, rfl, rfl, by lk [t2, t1]; exact lb, by lk [t2, t1]; exact ln, by lk [t2, t1]; exact ll,
      ⟨_, by lk [t2, t1]; rfl⟩, ⟨we, by lk [t2, t1]; exact le⟩, v + 1, true, [], wr, by omega, by simp,
      by lk [t2], by lk [t2, t1]; rw [lw]; rfl, by lk [t2, t1]; rw [lm]; rfl, by lk [t2, t1]; exact lr,
      fun h => absurd h (by simp), Or.inl ⟨by lk [t2, t1]; exact lg, rfl⟩⟩
  rcases olLoop_spec t2 A b hp (bytesAt_congr hb rfl rfl rfl) item sc (hit.congr rfl) J hJ _ t2 h0 with
    hs | ⟨hn, hI, hg⟩
  · exact Or.inl (seq_stop t2 _ _ hs)
  obtain ⟨m', d', c', g', b', -, -, -, -, -, j, wm, acc, wr', hj, hacc, li', -, lm', lr', hpos', br⟩ := hI
  have hR := (br.resolve_left (fun ⟨h1, _⟩ => by rw [hg] at h1; cases h1)).2
  generalize hu : evaluateHOLFiniteState t2 (.while (vv sG) (olBody item)) = r at hn li' lm' lr' m' d' c' g' b'
  obtain ⟨r1, r2⟩ := r
  simp only at hn li' lm' lr' m' d' c' g' b'
  subst hn
  unfold RetP
  rw [seq_normal _ hu]
  have hok : objListOpen sc b v = .ok acc.reverse j := by rw [hopen, hR]
  have hlen : acc.reverse.length ≤ j.toNat := by simpa using hacc
  rcases hret with rfl | rfl | rfl
  · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv r2 sI _ li'
    exact Or.inr ⟨_, q1, ⟨acc.reverse, j, hok, hj, hlen, fun _ => rfl, fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩, q2.trans m', q3.trans d', q4.trans g', q5.trans c', q6.trans b'⟩
  · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv r2 sM _ lm'
    exact Or.inr ⟨_, q1, ⟨acc.reverse, j, hok, hj, hlen, fun h => absurd h (by decide), fun _ => by simp,
      fun h => absurd h (by decide)⟩, q2.trans m', q3.trans d', q4.trans g', q5.trans c', q6.trans b'⟩
  · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv r2 sR _ lr'
    refine Or.inr ⟨_, q1, ⟨acc.reverse, j, hok, hj, hlen, fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun _ hJl => ?_⟩, q2.trans m', q3.trans d', q4.trans g', q5.trans c', q6.trans b'⟩
    exact hpos' (by simpa using hJl)

theorem olFun4_sound {α : Type} (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (item : MlS) (sc : ByteArray → USize → ScanRes α) (hit : ItemSound t item sc)
    (ret : MlS) (hret : ret = sI ∨ ret = sM ∨ ret = sR) (v : USize) (hv : v.toNat ≤ b.size) (J : Nat)
    (hJ : J < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J)))) :
    RetP t (olFun4 item ret) (OlPost b sc ret v J) := by
  unfold olFun4
  apply retP_decsOf
  simp only [olLocals, List.foldl]
  refine olCore_sound _ A b hp ?_ item sc ?_ ret hret v hv J hJ
    ?_ ?_ ?_ ?_ ⟨0, ?_⟩ ⟨0, ?_⟩ ?_ ?_ ?_ ⟨0, ?_⟩
  · exact bytesAt_congr hb rfl rfl rfl
  · exact hit.congr rfl
  · lk; exact lb
  · lk; exact ln
  · lk; exact li
  · lk; exact ll
  all_goals lk

theorem olFun3_sound {α : Type} (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (item : MlS) (sc : ByteArray → USize → ScanRes α) (hit : ItemSound t item sc)
    (ret : MlS) (hret : ret = sI ∨ ret = sM ∨ ret = sR) (v : USize) (hv : v.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat)))) :
    RetP t (olFun3 item ret) (OlPost b sc ret v 0) := by
  unfold olFun3
  apply retP_decsOf
  simp only [olLocals, List.foldl]
  refine olCore_sound _ A b hp ?_ item sc ?_ ret hret v hv 0 (by decide)
    ?_ ?_ ?_ ?_ ⟨0, ?_⟩ ⟨0, ?_⟩ ?_ ?_ ?_ ⟨0, ?_⟩
  · exact bytesAt_congr hb rfl rfl rfl
  · exact hit.congr rfl
  · lk; exact lb
  · lk; exact ln
  · lk; exact li
  all_goals (lk <;> rfl)

/-- The list's end function is a sound `.sub` callee for the list scanner. -/
theorem subSound_of_list {α : Type} (t : PanSemStateFiniteExact 64 σ) (fid : Nat) (item : MlS)
    (sc : ByteArray → USize → ScanRes α) (scU : ByteArray → USize → ScanRes Unit)
    (hU : ∀ b v e, scU b v = .ok () e ↔ ∃ xs, objListOpen sc b v = .ok xs e)
    (hcode : t.code.lookup (subName fid) = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 item sI, .one))
    (hit : ItemSound t item sc) : SubSound t fid scU := by
  refine ⟨_, hcode, fun s A b hsc hp hb v hv lb ln li => ?_⟩
  refine retP_mono (olFun3_sound s A b hp hb item sc (hit.congr hsc) sI (Or.inl rfl) v hv lb ln li) ?_
  rintro w ⟨xs, e, hok, he, -, hw, -, -⟩
  exact ⟨e, hw rfl, he, (), (hU b v e).mpr ⟨xs, hok⟩⟩

end

end ConPanqueque.Scan
