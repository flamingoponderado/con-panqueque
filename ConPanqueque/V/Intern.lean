import ConPanqueque.V.Ins
import ConPanqueque.ConsTbl
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning into one tier of a generic cons table

The twin's per-tier step at any constructor (`tierInt`): the cons probe,
then on a miss the append with handle `mkI size`. In Pancake (`internV`): hash
the key words, probe, then return the hit's handle or append and return the
new one. A handle's word is `base + index` (both of con-ron's layouts, below
their capacities), `base` read from the local `chb`.
-/

namespace ConPanqueque.V

def lHb := ofString "chb"
def lI := ofString "ci"

/-- The twin's per-tier intern: `find?`, else `push` with handle `mkI size`. -/
def tierInt {α ι δ : Type} [BEq α] [Hashable α] (tb : Tbl α ι δ) (x : α) (d : δ) (mkI : Nat → ι) : Tbl α ι δ × ι :=
  match tb.find? x with
  | some h => (tb, h)
  | none => (tb.push x d (mkI tb.size), mkI tb.size)

def hE (e : ExpHOL 64) : ExpHOL 64 := .op .add [vv lHb, e]

def internV : ProgHOL 64 :=
  .dec lWa .one (vv lK) (.dec lWb .one (.const 0) (.dec lWn .one (vv lL) (.dec lWeq .one (.const 0)
  (.dec lWg .one (.const 1) (.dec lWh .one (.const 0)
  (.seq hashLoop
  (.dec lJ .one (.op .and [vv lWh, vv lM]) (.dec lC .one (.op .add [vv lM, .const 1])
  (.dec lG .one (.const 1) (.dec lRes .one (.const 0) (.dec lV .one (.const 0)
  (.seq probeLoop
   (.ite (.cmp .notEqual (vv lRes) (.const 0)) (.return (hE (.op .sub [vv lRes, .const 1])))
    (.ite (.cmp .equal (vv lC) (.const 0)) hang
     (.dec lI .one (.load .one (vv lC0)) (.seq insBody (.return (hE (vv lI)))))))))))))))))))

/-- The home slot: the key words' hash, masked to `2^b` slots. -/
def homeV {α : Type} (enc : α → List (BitVec 64)) (b : Nat) (x : α) : Nat := (hashW (enc x)).toNat % 2 ^ b

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

omit [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] in
theorem vt_of_eq {t t' : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {rows : List α}
    {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {g : VGeo} {hu : Nat} (h : VT t enc rows ders slots g hu)
    (hm : t'.memory = t.memory) (hd : t'.memaddrs = t.memaddrs) : VT t' enc rows ders slots g hu := by
  obtain ⟨hs, hr, hsh, ⟨c1, c2⟩, ⟨p1, p2⟩, hle', hdl, hder, hle, hroom, hhr, l1, l2, l3, l4, l5⟩ := h
  refine ⟨fun j hj => ?_, fun i hi => ?_, hsh, ⟨by rw [hd]; exact c1, by rw [hm]; exact c2⟩,
    ⟨by rw [hd]; exact p1, by rw [hm]; exact p2⟩, hle', hdl, fun i hi => ?_, hle, fun i hi => ?_,
    fun k hk => by rw [hd]; exact hhr k hk, l1, l2, l3, l4, l5⟩
  · obtain ⟨v, a1, a2, a3, a4⟩ := hs j hj; exact ⟨v, a1, a2, by rw [hd]; exact a3, by rw [hm]; exact a4⟩
  · obtain ⟨P, a1, a2, a3, a4, a5, a6, a7⟩ := hr i hi
    exact ⟨P, by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hm]; exact a3, by rw [hm]; exact a4,
      fun k hk => by rw [hd, hm]; exact a5 k hk, a6, a7⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hder i hi
    exact ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hm]; exact a3, by rw [hm]; exact a4⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hroom i hi
    exact ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hd]; exact a3, by rw [hd]; exact a4⟩

/-- What `internV` guarantees: a stop, or the twin's handle with the twin's new table represented and
memory outside the table unchanged. Insensitive to the final locals. -/
def VRes (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hwd : ι → BitVec 64) (mkI : Nat → ι) (tb : Tbl α ι δ) (g : VGeo) (x : α) (d : δ)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨
    (r.1 = some (.returned (.val (.word (hwd (tierInt tb x d mkI).2)))) ∧
      ∃ rows' ders' slots' hu', VT r.2 enc rows' ders' slots' g hu' ∧ Inv (α := α) (homeV enc g.b) rows' slots' g.n ∧
        TblRel (tierInt tb x d mkI).1 rows' mkI ∧ (tierInt tb x d mkI).1.der.toList.map dW = ders' ∧
        r.2.code = t.code ∧ r.2.globals = t.globals ∧ r.2.memaddrs = t.memaddrs ∧ r.2.topAddr = t.topAddr ∧
        ∀ c, ¬ inR g c → r.2.memory c = t.memory c)

theorem vres_locals {t : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64}
    {hwd : ι → BitVec 64} {mkI : Nat → ι} {tb : Tbl α ι δ} {g : VGeo} {x : α} {d : δ}
    {r1 : Option (PanSemResultExact 64)} {st : PanSemStateFiniteExact 64 σ} (L : HolFiniteMapExact MlS (ValueHOL 64))
    (h : VRes t enc dW hwd mkI tb g x d (r1, st)) : VRes t enc dW hwd mkI tb g x d (r1, { st with locals := L }) := by
  rcases h with h | ⟨hr, rows', ders', slots', hu', hT, hi, hrel, hd, c1, c2, c3, c4, c5⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr, rows', ders', slots', hu', vt_of_eq hT rfl rfl, hi, hrel, hd, c1, c2, c3, c4, c5⟩

end

theorem mask_home (w : BitVec 64) (b : Nat) (hb : b ≤ 56) :
    w &&& BitVec.ofNat 64 (2 ^ b - 1) = BitVec.ofNat 64 (w.toNat % 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ b ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hb
  have h2 : (2 : Nat) ^ 56 < 2 ^ 64 := by decide
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 2 ^ b - 1) (by omega),
    Nat.mod_eq_of_lt (a := w.toNat % 2 ^ b) (by have := Nat.mod_lt w.toNat (Nat.two_pow_pos b); omega)]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat b

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

theorem internV_spec (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hwd : ι → BitVec 64) (mkI : Nat → ι) (base : BitVec 64) (icap : Nat)
    (hmk : ∀ i, i < icap → hwd (mkI i) = base + BitVec.ofNat 64 i) (hinj : ∀ x y, enc x = enc y → x = y)
    (tb : Tbl α ι δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat) (g : VGeo)
    (x : α) (d : δ) (K : BitVec 64)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30) (hci : g.cap ≤ icap)
    (hT : VT t enc rows ders slots g hu) (hinv : Inv (α := α) (homeV enc g.b) rows slots g.n)
    (hrel : TblRel tb rows mkI) (hder : tb.der.toList.map dW = ders)
    (hK : Words t K (enc x)) (hKl : (enc x).length < 2 ^ 61)
    (hKout : ∀ i, i < (enc x).length → ¬ inR g (K + BitVec.ofNat 64 (8 * i)))
    (lK' : t.locals.lookup lK = some (.val (.word K)))
    (ll : t.locals.lookup lL = some (.val (.word (BitVec.ofNat 64 (enc x).length))))
    (lm : t.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (g.n - 1)))))
    (ls : t.locals.lookup lS = some (.val (.word g.S))) (lr : t.locals.lookup lR = some (.val (.word g.R)))
    (lc : t.locals.lookup lC0 = some (.val (.word g.C)))
    (lcap : t.locals.lookup lCap = some (.val (.word (BitVec.ofNat 64 g.cap))))
    (ld : t.locals.lookup lD = some (.val (.word g.D)))
    (ldv : t.locals.lookup lDv = some (.val (.word (dW d).1)))
    (ldv2 : t.locals.lookup lDv2 = some (.val (.word (dW d).2)))
    (lke : t.locals.lookup lKe = some (.val (.word (g.KH + BitVec.ofNat 64 (8 * g.kcap)))))
    (lhb : t.locals.lookup lHb = some (.val (.word base))) :
    VRes t enc dW hwd mkI tb g x d (evaluateHOLFiniteState t internV) := by
  have hn56 : g.n ≤ 2 ^ 56 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
  have hpos : 0 < g.n := hinv.pos
  let hx := homeV enc g.b x
  have hxn : hx < g.n := hinv.home_lt x
  -- the scratch locals
  unfold internV
  obtain ⟨L1, e1⟩ := dec_word' t lWa (vv lK) K _ (eval_vv t lK _ lK')
  rw [e1]; apply vres_locals
  let t1 := setVarHOLFinite lWa (.val (.word K)) t
  obtain ⟨L2, e2⟩ := dec_word' t1 lWb (.const 0) 0 _ (eval_const t1 0)
  rw [e2]; apply vres_locals
  let t2 := setVarHOLFinite lWb (.val (.word 0)) t1
  obtain ⟨L3, e3⟩ := dec_word' t2 lWn (vv lL) _ _ (eval_vv t2 lL _ (by lk [t2, t1]; exact ll))
  rw [e3]; apply vres_locals
  let t3 := setVarHOLFinite lWn (.val (.word (BitVec.ofNat 64 (enc x).length))) t2
  obtain ⟨L4, e4⟩ := dec_word' t3 lWeq (.const 0) 0 _ (eval_const t3 0)
  rw [e4]; apply vres_locals
  let t4 := setVarHOLFinite lWeq (.val (.word 0)) t3
  obtain ⟨L5, e5⟩ := dec_word' t4 lWg (.const 1) 1 _ (eval_const t4 1)
  rw [e5]; apply vres_locals
  let t5 := setVarHOLFinite lWg (.val (.word 1)) t4
  obtain ⟨L6, e6⟩ := dec_word' t5 lWh (.const 0) 0 _ (eval_const t5 0)
  rw [e6]; apply vres_locals
  let t6 := setVarHOLFinite lWh (.val (.word 0)) t5
  have l6 : ∀ y, y ≠ lWh → y ≠ lWg → y ≠ lWeq → y ≠ lWn → y ≠ lWb → y ≠ lWa →
      t6.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6; lk [t6, t5, t4, t3, t2, t1]
  -- hashing
  rcases hashLoop_spec t6 K (enc x) (by omega) hK (by lk [t6, t5, t4, t3, t2, t1])
      (by lk [t6, t5, t4, t3]) (by lk [t6]) (by lk [t6, t5]) with hs | ⟨hn1, hHI, hwh⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  generalize hh : evaluateHOLFiniteState t6 hashLoop = hst at hn1 hHI hwh
  obtain ⟨h1r, h1⟩ := hst
  simp only at hn1 hHI hwh; subst hn1
  rw [seq_normal _ hh]
  obtain ⟨hm1, hd1, hc1, hg1, ht1, hfr1, k1, _, hwa1, hwn1, hbr1⟩ := hHI
  have hwg1 : ∃ z, h1.locals.lookup lWg = some (.val (.word z)) := by
    rcases hbr1 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact ⟨_, h⟩
  have k1' : ∀ y, y ≠ lWh → y ≠ lWg → y ≠ lWn → y ≠ lWa → h1.locals.lookup y = t6.locals.lookup y :=
    fun y a1 a2 a3 a4 => hfr1 y a4 a3 a1 a2
  have lM1 : h1.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (g.n - 1)))) := by
    rw [k1' _ (by decide) (by decide) (by decide) (by decide)]; lk [t6, t5, t4, t3, t2, t1]; exact lm
  have hJv : @evalHOLExact 64 σ _ h1.toExact (fun a => Classical.propDecidable (h1.memaddrs a))
      (.op .and [vv lWh, vv lM]) = some (.val (.word (BitVec.ofNat 64 hx))) := by
    simp [vv, evalHOLExact, evalListHOLExact, hwh, lM1, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [show (g.n - 1) = 2 ^ g.b - 1 by rw [hn]]
    show _ &&& (_ &&& (18446744073709551615#64)) = _
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes, mask_home _ _ hb]
    rfl
  obtain ⟨L7, e7⟩ := dec_word' h1 lJ _ _ _ hJv
  rw [e7]; apply vres_locals
  let u1 := setVarHOLFinite lJ (.val (.word (BitVec.ofNat 64 hx))) h1
  obtain ⟨L8, e8⟩ := dec_word' u1 lC (.op .add [vv lM, .const 1]) (BitVec.ofNat 64 g.n) _
    (by rw [eval_add2 u1 _ _ _ _ (eval_vv u1 lM _ (by lk [u1]; exact lM1)) (eval_const u1 1)]
        congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
  rw [e8]; apply vres_locals
  let u2 := setVarHOLFinite lC (.val (.word (BitVec.ofNat 64 g.n))) u1
  obtain ⟨L9, e9⟩ := dec_word' u2 lG (.const 1) 1 _ (eval_const u2 1)
  rw [e9]; apply vres_locals
  let u3 := setVarHOLFinite lG (.val (.word 1)) u2
  obtain ⟨L10, e10⟩ := dec_word' u3 lRes (.const 0) 0 _ (eval_const u3 0)
  rw [e10]; apply vres_locals
  let u4 := setVarHOLFinite lRes (.val (.word 0)) u3
  obtain ⟨L11, e11⟩ := dec_word' u4 lV (.const 0) 0 _ (eval_const u4 0)
  rw [e11]; apply vres_locals
  let u5 := setVarHOLFinite lV (.val (.word 0)) u4
  -- lookups of the inputs in `u5`, through the hash's frame
  have back : ∀ y, y ∉ scr → y ≠ lWh → u5.locals.lookup y = t.locals.lookup y := by
    intro y hy hh'
    simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hy
    lk [u5, u4, u3, u2, u1]
    rw [k1' y hh' n10 n8 n6]; lk [t6, t5, t4, t3, t2, t1]
  have hmem5 : u5.memory = t.memory := hm1
  have hd5 : u5.memaddrs = t.memaddrs := hd1
  have hT5 : VT u5 enc rows ders slots g hu := vt_of_eq hT hmem5 hd5
  have hK5 : Words u5 K (enc x) := fun k hk => by rw [hmem5, hd5]; exact hK k hk
  let ans := probeR rows slots g.n x g.n hx
  have hB5 : Base u5 u5 g.n g.S g.R K (enc x).length :=
    ⟨rfl, rfl, rfl, rfl, rfl, by rw [back _ (by decide) (by decide)]; exact ls,
      by rw [back _ (by decide) (by decide)]; exact lr, by rw [back _ (by decide) (by decide)]; exact lm,
      by rw [back _ (by decide) (by decide)]; exact lK', by rw [back _ (by decide) (by decide)]; exact ll,
      fun _ _ => rfl, fun y hy => by
        simp only [cscr, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, by lk [u5, u4, u3, u2, u1]; exact hwa1⟩
        · exact ⟨0, by lk [u5, u4, u3, u2, u1]; rw [k1' _ (by decide) (by decide) (by decide) (by decide)]; lk [t6, t5, t4, t3, t2]⟩
        · exact ⟨_, by lk [u5, u4, u3, u2, u1]; exact hwn1⟩
        · exact ⟨0, by lk [u5, u4, u3, u2, u1]; rw [k1' _ (by decide) (by decide) (by decide) (by decide)]; lk [t6, t5, t4]⟩
        · obtain ⟨z, hz⟩ := hwg1; exact ⟨z, by lk [u5, u4, u3, u2, u1]; exact hz⟩⟩
  have hI : LInv u5 enc rows slots g.n g.S g.R K x ans u5 :=
    ⟨hB5, g.n, hx, hxn, by lk [u5, u4, u3, u2, u1], by lk [u5, u4, u3, u2, u1], ⟨0, by lk [u5]⟩,
      Or.inl ⟨by lk [u5, u4, u3, u2, u1], by lk [u5, u4, u3, u2, u1], rfl, Nat.le_refl _⟩⟩
  rcases probeLoop_spec u5 enc rows slots g.n g.b g.S g.R K x ans hn (by omega) hT5.vmem hK5 hKl hinv.named hinj u5 hI
    with hs | ⟨hn6, hI6, hg6⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  generalize hp : evaluateHOLFiniteState u5 probeLoop = pst at hn6 hI6 hg6
  obtain ⟨p1, u⟩ := pst
  simp only at hn6 hI6 hg6; subst hn6
  rw [seq_normal _ hp]
  obtain ⟨hB6, f, j, hj, hC6, hJ6, hV6, br⟩ := hI6
  obtain ⟨_, hres6, hemp, hfull⟩ := br.resolve_left (fun ⟨hg, _⟩ => by rw [hg6] at hg; cases hg)
  have hprobe := probeR_toOpt rows slots g.n x g.n hx
  have hfind := find_probe (homeV enc g.b) tb rows slots g.n mkI hrel hinv x
  have uback : ∀ y, y ∉ scr → y ≠ lWh → u.locals.lookup y = t.locals.lookup y := fun y hy hh' => by
    rw [hB6.fr y hy]; exact back y hy hh'
  have hmu : u.memory = t.memory := by rw [hB6.mem, hmem5]
  have hdu : u.memaddrs = t.memaddrs := by rw [hB6.addrs, hd5]
  have hcu : u.code = t.code := by rw [hB6.code]; exact hc1
  have hgu : u.globals = t.globals := by rw [hB6.globals]; exact hg1
  have htu : u.topAddr = t.topAddr := by rw [hB6.top]; exact ht1
  have hlhb : u.locals.lookup lHb = some (.val (.word base)) := by rw [uback _ (by decide) (by decide)]; exact lhb
  cases hto : ans.toOpt with
  | some i =>
    rw [hto] at hres6
    simp only [Option.map_some, Option.getD_some] at hres6
    have hi : rows[i]? = some x := (probe_correct (homeV enc g.b) rows slots g.n hinv x).1 i (by rw [← hprobe]; exact hto)
    have hil : i < rows.length := (List.getElem?_eq_some_iff.mp hi).1
    have hcapl := hT.le
    have hne : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .notEqual (vv lRes) (.const 0)) = some (.val (.word 1)) := by
      rw [ConsLoop.eval_cmp_of u .notEqual _ _ _ 0 (eval_vv u lRes _ hres6) (eval_const u 0)]
      have : ¬ BitVec.ofNat 64 (i + 1) = 0 := fun e => by have := congrArg BitVec.toNat e; simp at this; omega
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact this
    rw [ite_word u _ _ _ _ hne]
    simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
    have hw : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (hE (.op .sub [vv lRes, .const 1])) = some (.val (.word (hwd (mkI i)))) := by
      rw [hmk i (by omega)]
      unfold hE
      rw [eval_add2 u _ _ _ _ (eval_vv u lHb _ hlhb) (eval_sub2 u _ _ _ _ (eval_vv u lRes _ hres6) (eval_const u 1))]
      congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega
    have eret : evaluateHOLFiniteState u (.return (hE (.op .sub [vv lRes, .const 1]))) =
        (some (.returned (.val (.word (hwd (mkI i))))), emptyLocalsHOLFinite u) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only [hw]; simp [shapeOfHOLExact]
    rw [eret]
    have hfi : tb.find? x = some (mkI i) := by rw [hfind, ← hprobe, hto]; rfl
    have htA : tierInt tb x d mkI = (tb, mkI i) := by simp only [tierInt, hfi]
    unfold VRes; rw [htA]
    exact Or.inr ⟨rfl, rows, ders, slots, hu, vt_of_eq hT hmu hdu, hinv, hrel, hder,
      hcu, hgu, hdu, htu,
      fun c _ => by rw [show (emptyLocalsHOLFinite u).memory = u.memory from rfl, hmu]⟩
  | none =>
    rw [hto] at hres6
    simp only [Option.map_none, Option.getD_none] at hres6
    have hne : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .notEqual (vv lRes) (.const 0)) = some (.val (.word 0)) := by
      rw [ConsLoop.eval_cmp_of u .notEqual _ _ _ 0 (eval_vv u lRes _ hres6) (eval_const u 0)]
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [ite_word u _ _ _ _ hne]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    have hce : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.cmp .equal (vv lC) (.const 0)) = some (.val (.word (bw (BitVec.ofNat 64 f = 0)))) := by
      rw [ConsLoop.eval_cmp_of u .equal _ _ _ 0 (eval_vv u lC _ hC6) (eval_const u 0)]
      by_cases h : BitVec.ofNat 64 f = 0 <;> simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [ite_word u _ _ _ _ hce]
    by_cases hf0 : BitVec.ofNat 64 f = 0
    · simp only [bw, hf0, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact Or.inl (Or.inl (hang_spec _ u rfl))
    simp only [bw, hf0, ↓reduceIte, ne_eq, not_true_eq_false]
    have hnf : ans ≠ .full := fun e => hf0 (by rw [hfull.mp e]; rfl)
    obtain ⟨j0, hans⟩ : ∃ j0, ans = .empty j0 := by
      revert hto hnf; cases ans with
      | hit i => intro h; cases h
      | empty j0 => intro _ _; exact ⟨j0, rfl⟩
      | full => intro _ h; exact absurd rfl h
    have hjj : j0 = j := hemp j0 hans
    have hcnt : u.memaddrs g.C ∧ u.memory g.C = .word (BitVec.ofNat 64 rows.length) := by
      rw [hmu, hdu]; exact hT.cnt
    have hld : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.load .one (vv lC0)) = some (.val (.word (BitVec.ofNat 64 rows.length))) := by
      rw [eval_load_word u _ _ (eval_vv u lC0 _ (by rw [uback _ (by decide) (by decide)]; exact lc)) hcnt.1, hcnt.2]
    obtain ⟨L12, e12⟩ := dec_word' u lI _ _ _ hld
    rw [e12]; apply vres_locals
    let w0 := setVarHOLFinite lI (.val (.word (BitVec.ofNat 64 rows.length))) u
    have wback : ∀ y, y ∉ scr → y ≠ lWh → y ≠ lI → w0.locals.lookup y = t.locals.lookup y := by
      intro y h1 h2 h3; lk [w0]; exact uback y h1 h2
    have hxr : x ∉ rows := (probe_correct (homeV enc g.b) rows slots g.n hinv x).2.mp (by rw [← hprobe]; exact hto)
    rcases ins_spec w0 g enc rows ders slots hu x (dW d).1 (dW d).2 K j (vt_of_eq hT hmu hdu) hj hcap hn56
        (fun k hk => by show u.memaddrs _ ∧ u.memory _ = _; rw [hmu, hdu]; exact hK k hk) hKl hKout
        (by rw [wback _ (by decide) (by decide) (by decide)]; exact lc)
        (by rw [wback _ (by decide) (by decide) (by decide)]; exact lcap)
        (by lk [w0]; exact hB6.r) (by rw [wback _ (by decide) (by decide) (by decide)]; exact ld)
        (by lk [w0]; exact hB6.s) (by lk [w0]; exact hJ6) (by lk [w0]; exact hB6.k) (by lk [w0]; exact hB6.l)
        (by rw [wback _ (by decide) (by decide) (by decide)]; exact ldv)
        (by rw [wback _ (by decide) (by decide) (by decide)]; exact ldv2)
        (by rw [wback _ (by decide) (by decide) (by decide)]; exact lke)
        (fun y hy => by
          have : y ≠ lI := fun e => by subst e; revert hy; decide
          obtain ⟨z, hz⟩ := hB6.cw y hy; exact ⟨z, by lk [w0]; exact hz⟩)
      with hs | ⟨hn7, hlt, hVT, hd7, hc7, hg7, ht7, hm7, hl7⟩
    · exact Or.inl (seq_stop _ _ _ hs)
    generalize hiw : evaluateHOLFiniteState w0 insBody = ist at hn7 hVT hd7 hc7 hg7 ht7 hm7 hl7
    obtain ⟨i1, w⟩ := ist
    simp only at hn7 hVT hd7 hc7 hg7 ht7 hm7 hl7; subst hn7
    rw [seq_normal _ hiw]
    have wI : w.locals.lookup lI = some (.val (.word (BitVec.ofNat 64 rows.length))) := by
      rw [hl7 _ (by simp) (by decide)]; lk [w0]
    have wHb : w.locals.lookup lHb = some (.val (.word base)) := by
      rw [hl7 _ (by simp) (by decide), wback _ (by decide) (by decide) (by decide)]; exact lhb
    have hw : @evalHOLExact 64 σ _ w.toExact (fun a => Classical.propDecidable (w.memaddrs a)) (hE (vv lI)) =
        some (.val (.word (hwd (mkI rows.length)))) := by
      rw [hmk _ (by omega)]; unfold hE; rw [eval_add2 w _ _ _ _ (eval_vv w lHb _ wHb) (eval_vv w lI _ wI)]
    have eret : evaluateHOLFiniteState w (.return (hE (vv lI))) =
        (some (.returned (.val (.word (hwd (mkI rows.length))))), emptyLocalsHOLFinite w) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only [hw]; simp [shapeOfHOLExact]
    rw [eret]
    have hfi : tb.find? x = none := by rw [hfind, ← hprobe, hto]; rfl
    have hsz : tb.size = rows.length := by show tb.nodes.size = _; rw [← hrel.1, Array.length_toList]
    have htA : tierInt tb x d mkI = (tb.push x d (mkI rows.length), mkI rows.length) := by
      simp only [tierInt, hfi, hsz]
    have hpe : probeR rows slots g.n x g.n (at_ g.n hx 0) = .empty j0 := by
      rw [show at_ g.n hx 0 = hx by simp only [at_, Nat.add_zero]; exact Nat.mod_eq_of_lt hxn]; exact hans
    obtain ⟨d', hd', hjd⟩ := probeR_empty rows slots g.n hx x hpos g.n 0 j0 hpe
    unfold VRes; rw [htA]
    refine Or.inr ⟨rfl, rows ++ [x], ders ++ [((dW d).1, (dW d).2)], slots.set j (rows.length + 1), hu + (enc x).length,
      vt_of_eq hVT rfl rfl, ?_, push_rel tb rows mkI hrel x d hxr, by simp [Tbl.push, ← hder], hc7.trans hcu,
      hg7.trans hgu, hd7.trans hdu, ht7.trans htu, fun c hc => by rw [show (emptyLocalsHOLFinite w).memory = w.memory from rfl, hm7 c hc]; exact congrFun hmu c⟩
    rw [← hjj, hjd]; exact insert_inv (homeV enc g.b) rows slots g.n hinv x hxr d' hd'

end

end ConPanqueque.V
