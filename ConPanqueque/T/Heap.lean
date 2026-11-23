import ConPanqueque.T.MemoClear
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The value heap in a caller

The context's image `C.H` is a prefix of the heap. A caller that allocates switches to the context
`ctxH C H'` whose image is the current heap (plus the cells it just took); every spec stated at `C`
still holds there (`sr_weakenH`). Cells the caller owns (allocated by it, past every image anyone
else holds facts about) may be overwritten, the image following along.
-/

namespace ConPanqueque.T

variable {σ : Type}

def ctxH (C : Ctx) (H : List (BitVec 64)) : Ctx := { C with H := H }

/-- Heap cell `j`. -/
def cellA (C : Ctx) (j : Nat) : BitVec 64 := C.HB + BitVec.ofNat 64 (8 * j)

theorem ctxOK_H {C : Ctx} (hok : CtxOK C) (H : List (BitVec 64)) : CtxOK (ctxH C H) := by
  cases hok; constructor <;> assumption

theorem sr_weakenH {C : Ctx} {s : AState} {t : PState σ} {H : List (BitVec 64)} (h : SR (ctxH C H) s t)
    (hp : C.H <+: H) : SR C s t :=
  ⟨h.rep, h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf, h.memo, h.memoN, h.cache, h.mode, h.env, h.pins,
    let ⟨H', hp', ha⟩ := h.heap; ⟨H', hp.trans hp', ha⟩⟩

theorem sr_exactH {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) (H : List (BitVec 64))
    (ha : HeapAt t C.HB C.HN H) : SR (ctxH C H) s t :=
  ⟨h.rep, h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf, h.memo, h.memoN, h.cache, h.mode, h.env, h.pins, ⟨H, List.prefix_refl _, ha⟩⟩

theorem inv_weakenH {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {t : PState σ}
    {H : List (BitVec 64)} (h : Inv (ctxH C H) s Γ M D t) (hp : C.H <+: H) : Inv C s Γ M D t :=
  ⟨sr_weakenH h.sr hp, h.env, h.mem, h.decl⟩

/-- A spec at the smaller image holds at any bigger one. -/
theorem specR_weakenH {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {H : List (BitVec 64)} (hp : C.H <+: H)
    (h : SpecR (Inv C s Γ M D) c s m R) : SpecR (Inv (ctxH C H) s Γ M D) c s m R :=
  fun t ht => h t (inv_weakenH ht hp)

theorem cell_inj {C : Ctx} (lay : C.HB.toNat + 8 * C.HN < 2 ^ 64) {i j : Nat} (hi : i < C.HN) (hj : j < C.HN)
    (e : cellA C i = cellA C j) : i = j := by
  have := congrArg BitVec.toNat e
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (show 8 * i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show C.HB.toNat + 8 * i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show C.HB.toNat + 8 * j < 2 ^ 64 by omega)] at this
  omega

theorem heap_cell {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) (j : Nat) (hj : j < C.H.length) :
    t.memaddrs (cellA C j) ∧ t.memory (cellA C j) = .word C.H[j] := by
  obtain ⟨H', hp, ha⟩ := h.heap
  have hl := hp.length_le
  refine ⟨ha.dom j (by have := ha.len; omega), ?_⟩
  rw [cellA, ha.val j (by omega), List.IsPrefix.getElem hp hj]

/-- `x := *(e)` at a cell of the image. -/
theorem specR_heapLoadI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (j : Nat)
    (hj : j < C.H.length) (hx : x ∈ D) (he : sev Γ e = some (cellA C j))
    (h : SpecR (Inv C s ((x, C.H[j]) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one e)) rest) s m R :=
  specR_pre_assign x (.load .one e) (fun _ => C.H[j])
    (fun t ht => by
      rw [EV, eval_load_word t _ _ (inv_ev ht he) (heap_cell ht.sr j hj).1, (heap_cell ht.sr j hj).2])
    (fun t ht => ht.decl x hx) (fun t ht => inv_set ht x _) h

/-! ## Overwriting an owned cell -/

theorem prefix_set {l₁ l₂ : List (BitVec 64)} (h : l₁ <+: l₂) (j : Nat) (hj : j < l₁.length) (w : BitVec 64) :
    l₁.set j w <+: l₂.set j w := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r, by rw [List.set_append_left _ _ hj]⟩

theorem sr_heapStore {C : Ctx} (hok : CtxOK C) {s : AState} {t : PState σ} (h : SR C s t) (j : Nat)
    (hj : j < C.H.length) (w : BitVec 64) :
    SR (ctxH C (C.H.set j w)) s
      { t with memory := fun c => if c = cellA C j then .word w else t.memory c } := by
  obtain ⟨H', hp, ha⟩ := h.heap
  have hl := hp.length_le
  have hjN : j < C.HN := by have := ha.len; omega
  have hne : ∀ c, c ≠ cellA C j →
      (fun c => if c = cellA C j then HolWordLab.word w else t.memory c) c = t.memory c :=
    fun c hc => by simp [hc]
  refine ⟨srep_frame h.rep ⟨hne _ (fun e => hok.flHeap j _ hjN (Or.inl rfl) e.symm),
      hne _ (fun e => hok.flHeap j _ hjN (Or.inr (Or.inl rfl)) e.symm),
      hne _ (fun e => hok.flHeap j _ hjN (Or.inr (Or.inr (Or.inl rfl))) e.symm),
      hne _ (fun e => hok.flHeap j _ hjN (Or.inr (Or.inr (Or.inr rfl))) e.symm)⟩ rfl
      (fun k tier hk ht => ⟨fun mm hm => hne _ (fun e => hok.dirHeap j k tier mm hjN hk ht hm e.symm),
        fun c hc => hne c (fun e => hok.heapOut j hjN ⟨k, tier, hk, ht, (e ▸ hc : inR _ (cellA C j))⟩)⟩),
    h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf,
    fun mk => memoAt_frame (h.memo mk) (fun c hc => hne c (fun e => hok.heapMemo (.e mk) j hjN (e ▸ hc : inR _ (cellA C j))))
      (fun k hk => hne _ (fun e => hok.mdescHeap (.e mk) j k hjN hk e.symm)) rfl,
    fun mk => memoAtN_frame (h.memoN mk) (fun c hc => hne c (fun e => hok.heapMemo (.n mk) j hjN (e ▸ hc : inR _ (cellA C j))))
      (fun k hk => hne _ (fun e => hok.mdescHeap (.n mk) j k hjN hk e.symm)) rfl,
    fun ck => cacheAt_frame (h.cache ck) (fun c hc => hne c (fun e => hok.heapMemo (.c ck) j hjN (e ▸ hc : inR _ (cellA C j))))
      (fun k hk => hne _ (fun e => hok.mdescHeap (.c ck) j k hjN hk e.symm)) rfl,
    modeAt_frame h.mode (fun b ck c hc => hne c (fun e => hok.heapMemo (.m b ck) j hjN (e ▸ hc : inR _ (cellA C j))))
      (fun b ck k hk => hne _ (fun e => hok.mdescHeap (.m b ck) j k hjN hk e.symm)) rfl rfl,
    envAt_frame h.env (fun b c hc => hne c (fun e => hok.heapMemo (envR b) j hjN (e ▸ hc : inR _ (cellA C j))))
      (fun b k hk => hne _ (fun e => hok.mdescHeap (envR b) j k hjN hk e.symm))
      (fun i hi => hne _ (fun e => hok.heapEnv j i hjN hi e.symm)) rfl ⟨rfl, rfl⟩, h.pins,
    ⟨H'.set j w, prefix_set hp j hj w, ?_⟩⟩
  refine ⟨by rw [List.length_set]; exact ha.top, by rw [List.length_set]; exact ha.len, ha.lay, ha.dom,
    fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.length_set] at hi
    show (if cellA C i = cellA C j then _ else _) = _
    by_cases e : i = j
    · subst e; simp
    · have : cellA C i ≠ cellA C j := fun x => e (cell_inj ha.lay (by have := ha.len; omega) hjN x)
      simp only [this, ite_false, List.getElem_set_ne (Ne.symm e)]
      exact ha.val i hi
  · show ∃ w', (if cellA C i = cellA C j then _ else _) = _
    by_cases e : i = j
    · subst e; exact ⟨w, by simp⟩
    · have : cellA C i ≠ cellA C j := fun x => e (cell_inj ha.lay hi hjN x)
      simp only [this, ite_false]
      exact ha.words i hi

/-- `*(ea) := ev` at a cell of the image: the image follows. Memory facts are dropped. -/
theorem specR_heapStoreI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (ea ev : ExpHOL 64) (j : Nat)
    (hj : j < C.H.length) (w : BitVec 64) (hea : sev Γ ea = some (cellA C j)) (hev : sev Γ ev = some w)
    (h : SpecR (Inv (ctxH C (C.H.set j w)) s Γ [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.store ea ev) rest) s m R := by
  refine specR_seq (fun t ht => ?_) h
  rw [store_word t ea ev _ w (inv_ev ht hea) (inv_ev ht hev) (heap_cell ht.sr j hj).1]
  exact Or.inr ⟨rfl, sr_heapStore hok ht.sr j hj w, fun y v hy => ht.env y v hy, fun _ _ h => absurd h (by simp),
    ht.decl⟩

/-! ## Allocation -/

/-- `x := Ght; if (HB + 8·HN − x < eN) hang; Ght := x + eN; rest` (`eN` is `8 n`). -/
def allocP (C : Ctx) (x : MlS) (eN : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local x (.var .global gHt))
    (.ite (.cmp .lower (.op .sub [.const (C.HB + BitVec.ofNat 64 (8 * C.HN)), vv x]) eN) hang
      (.seq (.assign .global gHt (.op .add [vv x, eN])) rest))

/-- The word a memory label holds (`0` for a non-word). -/
def labW : HolWordLab 64 → BitVec 64
  | .word w => w

theorem specR_allocI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (eN : ExpHOL 64)
    (n : Nat) (hn : 8 * n < 2 ^ 64) (hx : x ∈ D) (hN : ∀ v, sev ((x, v) :: Γ) eN = some (BitVec.ofNat 64 (8 * n)))
    (hk : ∀ (H' ws : List (BitVec 64)), C.H <+: H' → ws.length = n → H'.length + n ≤ C.HN →
      SpecR (Inv (ctxH C (H' ++ ws)) s ((x, cellA C H'.length) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (allocP C x eN rest) s m R := by
  intro t ht
  obtain ⟨H', hp, ha⟩ := ht.sr.heap
  obtain ⟨w0, hw0⟩ := ht.decl x hx
  unfold allocP
  rw [seq_normal _ (ConsLoop.assign_local t x _ (cellA C H'.length) w0 (by simp [evalHOLExact, ha.top]; rfl) hw0)]
  let t1 := setVarHOLFinite x (.val (.word (cellA C H'.length))) t
  have ht1 : Inv C s ((x, cellA C H'.length) :: Γ) M D t1 := inv_set ht x _
  have hlen := ha.len
  have lay := ha.lay
  have hfree : C.HB + BitVec.ofNat 64 (8 * C.HN) - cellA C H'.length = BitVec.ofNat 64 (8 * (C.HN - H'.length)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [cellA, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 8 * C.HN < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * H'.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show C.HB.toNat + 8 * C.HN < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show C.HB.toNat + 8 * H'.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 * (C.HN - H'.length) < 2 ^ 64 by omega)]
    omega
  have hc : EV t1 (.cmp .lower (.op .sub [.const (C.HB + BitVec.ofNat 64 (8 * C.HN)), vv x]) eN) =
      some (.val (.word (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower
        (BitVec.ofNat 64 (8 * (C.HN - H'.length))) (BitVec.ofNat 64 (8 * n)) then 1 else 0))) := by
    refine inv_ev ht1 ?_
    simp [sev, hN, hfree]
  rw [ite_word t1 _ _ _ _ hc]
  by_cases full : C.HN - H'.length < n
  · have : BitVec.ofNat 64 (8 * (C.HN - H'.length)) < BitVec.ofNat 64 (8 * n) := by
      rw [BitVec.lt_def]; simp; omega
    have hw1 : (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 (8 * (C.HN - H'.length)))
        (BitVec.ofNat 64 (8 * n)) then (1 : BitVec 64) else 0) = 1 := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
    rw [hw1, if_pos (by decide)]
    exact Or.inl (Or.inl (hang_spec t1.clock t1 rfl))
  have hnf : ¬ BitVec.ofNat 64 (8 * (C.HN - H'.length)) < BitVec.ofNat 64 (8 * n) := by
    rw [BitVec.lt_def]; simp; omega
  have hw0 : (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 (8 * (C.HN - H'.length)))
      (BitVec.ofNat 64 (8 * n)) then (1 : BitVec 64) else 0) = 0 := by
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnf]
  rw [hw0, if_neg (by decide)]
  have htop1 : t1.globals.lookup gHt = some (.val (.word (cellA C H'.length))) := ha.top
  rw [seq_normal _ (assign_ok t1 .global gHt _ (.val (.word (cellA C H'.length + BitVec.ofNat 64 (8 * n))))
    (by have := inv_ev ht1 (e := .op .add [vv x, eN]) (v := cellA C H'.length + BitVec.ofNat 64 (8 * n))
          (by simp [sev, hN]); exact this)
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, htop1, shapeOfHOLExact, shapeEqHOL]))]
  let t2 := setKvarHOLFinite .global gHt (.val (.word (cellA C H'.length + BitVec.ofNat 64 (8 * n)))) t1
  let ws : List (BitVec 64) := (List.range n).map fun i => labW (t.memory (cellA C (H'.length + i)))
  have hws : ws.length = n := by simp [ws]
  have hgl : ∀ y, y ≠ gHt → t2.globals.lookup y = t.globals.lookup y := fun y hy => by
    simp [t2, t1, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite, FUPDATE, Ne.symm hy]
  have hHA : HeapAt t2 C.HB C.HN (H' ++ ws) := by
    refine ⟨?_, by rw [List.length_append, hws]; omega, lay, fun i hi => ha.dom i hi, fun i hi => ?_,
      fun i hi => ha.words i hi⟩
    · have e8 : cellA C H'.length + BitVec.ofNat 64 (8 * n) = C.HB + BitVec.ofNat 64 (8 * (H' ++ ws).length) := by
        rw [List.length_append, hws]
        apply BitVec.eq_of_toNat_eq
        simp only [cellA, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show 8 * H'.length < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * n < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show 8 * (H'.length + n) < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show C.HB.toNat + 8 * H'.length < 2 ^ 64 by omega)]
        omega
      rw [← e8]
      simp [t2, setKvarHOLFinite, setGlobalHOLFinite, FUPDATE]
    · show t.memory _ = _
      rw [List.length_append, hws] at hi
      by_cases hl : i < H'.length
      · rw [List.getElem_append_left hl]; exact ha.val i hl
      · rw [List.getElem_append_right (by omega)]
        obtain ⟨w', hw'⟩ := ha.words i (by omega)
        simp only [ws, List.getElem_map, List.getElem_range]
        rw [show H'.length + (i - H'.length) = i by omega]
        show t.memory (cellA C i) = _
        rw [show cellA C i = C.HB + BitVec.ofNat 64 (8 * i) from rfl, hw']; rfl
  have hInv : Inv (ctxH C (H' ++ ws)) s ((x, cellA C H'.length) :: Γ) M D t2 := by
    have hsr1 := ht1.sr
    refine ⟨⟨srep_frame hsr1.rep ⟨rfl, rfl, rfl, rfl⟩ rfl (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩), by rw [hgl _ (by decide)]; exact ht.sr.gdir, by rw [hgl _ (by decide)]; exact ht.sr.gfln,
      by rw [hgl _ (by decide)]; exact ht.sr.gfll, by rw [hgl _ (by decide)]; exact ht.sr.gfls,
      by rw [hgl _ (by decide)]; exact ht.sr.gfle, by rw [hgl _ (by decide)]; exact ht.sr.gkb, hsr1.code,
      hsr1.kbuf, fun k => memoAt_of_eq (hsr1.memo k) rfl rfl, fun k => memoAtN_frame (hsr1.memoN k) (fun _ _ => rfl)
        (fun _ _ => rfl) rfl, fun k => cacheAt_frame (hsr1.cache k) (fun _ _ => rfl) (fun _ _ => rfl) rfl,
        modeAt_frame ht.sr.mode (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl (hgl _ (by decide)),
        envAt_frame ht.sr.env (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) rfl ⟨hgl _ (by decide), hgl _ (by decide)⟩, ht.sr.pins, ⟨H' ++ ws, List.prefix_refl _, hHA⟩⟩, ht1.env, ht1.mem, ht1.decl⟩
  exact hk H' ws hp hws (by omega) t2 hInv

end ConPanqueque.T

namespace ConPanqueque.T

/-- Memory changes beyond the context's image keep the heap: the new image is read off memory. -/
theorem heapEx_reframe {σ : Type} {t u : PanSemStateFiniteExact 64 σ} {HB : BitVec 64} {HN : Nat}
    {H : List (BitVec 64)} (h : HeapEx t HB HN H)
    (hm : ∀ i, i < H.length → u.memory (HB + BitVec.ofNat 64 (8 * i)) = t.memory (HB + BitVec.ofNat 64 (8 * i)))
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals.lookup gHt = t.globals.lookup gHt) : HeapEx u HB HN H := by
  obtain ⟨H', hp, ha⟩ := h
  refine ⟨(List.range H'.length).map (fun i => labW (u.memory (HB + BitVec.ofNat 64 (8 * i)))), ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := hp
    refine ⟨((List.range r.length).map (fun i => labW (u.memory (HB + BitVec.ofNat 64 (8 * (H.length + i)))))), ?_⟩
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_append, List.length_map, List.length_range] at h1 h2
      rw [List.getElem_map, List.getElem_range]
      by_cases hi : i < H.length
      · rw [List.getElem_append_left (by simpa using hi)]
        have := ha.val i (by simp; omega)
        rw [List.getElem_append_left hi] at this
        rw [hm i hi, this]; rfl
      · rw [List.getElem_append_right (by omega)]
        simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
        rw [show H.length + (i - H.length) = i by omega]
  · refine ⟨by rw [hg]; simpa using ha.top, by simpa using ha.len, ha.lay, fun i hi => by rw [hd]; exact ha.dom i hi,
      fun i hi => ?_, fun i hi => ⟨labW (u.memory _), by cases e : u.memory (HB + BitVec.ofNat 64 (8 * i)); rfl⟩⟩
    simp only [List.getElem_map, List.getElem_range]
    cases u.memory (HB + BitVec.ofNat 64 (8 * i)); rfl

end ConPanqueque.T
