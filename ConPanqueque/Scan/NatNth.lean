import ConPanqueque.Scan.LevPair

/-! # The `k`-th element of a number list, in Pancake

`nnFun(b, n, v, k)` walks the list at `v` as `lpFun` does (whitespace, a number, whitespace, a comma
or the close bracket) and returns its `k`-th element (capped at `natCap`), or `nnSent` when the list
has at most `k` elements.  `nnFun_sound`: when con-leche's `scanNatList b v` gives `us`, the returned
word is `us[k]` (capped) or the sentinel. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

/-- What con-leche's list loop already holds is a prefix of its answer. -/
theorem nlLoop_prefix (b : ByteArray) :
    ∀ msr (i : USize) (acc : List Nat) (w : Bool) (us : List Nat) (e : USize), b.size - i.toNat = msr →
      scanNatListLoop b i acc w = .ok us e → acc.reverse <+: us := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i acc w us e hn h
    rw [scanNatListLoop.eq_def] at h
    by_cases hi : i < b.usize
    · rw [dite_eq_left hi] at h
      have hs := usizeStep b i hi
      have hb := usizeInBounds b i hi
      generalize b.uget i (usizeInBounds b i hi) = c at h
      simp only at h
      split at h
      · exact ih _ (by omega) _ _ _ _ _ rfl h
      split at h
      · split at h
        · simp at h
        · simp only [ScanRes.ok.injEq] at h; rw [h.1]; exact List.prefix_refl _
      split at h
      · split at h
        · simp at h
        · exact ih _ (by omega) _ _ _ _ _ rfl h
      split at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · rename_i hie
              have := ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ rfl h
              exact (List.prefix_append _ _).trans (by simpa using this)
            · simp at h
      · simp at h
    · rw [dite_eq_right hi] at h; simp at h

theorem nlLoop_close0 {b : ByteArray} {p : USize} (h : p < b.usize) (hc : byteAt b p = 93) :
    scanNatListLoop b p [] true = .ok [] (p + 1) := by
  rw [byteAt_uget h] at hc
  rw [scanNatListLoop.eq_def b p [] true, dite_eq_left h, hc]
  rfl

section
variable {σ : Type}

/-- A statement that stops or finishes normally in a state satisfying `Q`. -/
def Ok (u : PanSemStateFiniteExact 64 σ) (c : ProgHOL 64) (Q : PanSemStateFiniteExact 64 σ → Prop) : Prop :=
  Stop (evaluateHOLFiniteState u c).1 ∨ ((evaluateHOLFiniteState u c).1 = none ∧ Q (evaluateHOLFiniteState u c).2)

theorem ok_seq {u u1 : PanSemStateFiniteExact 64 σ} {p q : ProgHOL 64} {Q : PanSemStateFiniteExact 64 σ → Prop}
    (h : evaluateHOLFiniteState u p = (none, u1)) (hq : Ok u1 q Q) : Ok u (.seq p q) Q := by
  unfold Ok at hq ⊢; rw [seq_normal _ h]; exact hq

theorem ok_hang (u : PanSemStateFiniteExact 64 σ) (Q : PanSemStateFiniteExact 64 σ → Prop) : Ok u hang Q :=
  Or.inl (stop_hang u)

theorem ok_ite {u : PanSemStateFiniteExact 64 σ} {e : ExpHOL 64} {p q : ProgHOL 64} {w : BitVec 64}
    {Q : PanSemStateFiniteExact 64 σ → Prop}
    (he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e =
      some (.val (.word w)))
    (hp : w ≠ 0 → Ok u p Q) (hq : w = 0 → Ok u q Q) : Ok u (.ite e p q) Q := by
  unfold Ok at hp hq ⊢
  rw [ite_word u _ _ _ _ he]
  by_cases hw : w = 0
  · simp only [hw, ne_eq, not_true_eq_false, ↓reduceIte]; exact hq hw
  · simp only [hw, ne_eq, not_false_eq_true, ↓reduceIte]; exact hp hw

theorem ok_assign {u : PanSemStateFiniteExact 64 σ} {x : MlS} {e : ExpHOL 64} {v w0 : BitVec 64}
    {Q : PanSemStateFiniteExact 64 σ → Prop}
    (he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e =
      some (.val (.word v)))
    (hx : u.locals.lookup x = some (.val (.word w0))) (hQ : Q (setVarHOLFinite x (.val (.word v)) u)) :
    Ok u (.assign .local x e) Q := by
  unfold Ok; rw [ConsLoop.assign_local u x e v w0 he hx]; exact Or.inr ⟨rfl, hQ⟩

theorem ok_call3 {s : PanSemStateFiniteExact 64 σ} {x f x1 x2 x3 : MlS} {body q : ProgHOL 64}
    {a1 a2 a3 : ExpHOL 64} {v1 v2 v3 v w0 : BitVec 64} {Q : PanSemStateFiniteExact 64 σ → Prop}
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
      callee.lookup x3 = some (.val (.word v3)) → RetSpec (callEntryStateHOLFinite s callee) body v)
    (k : ∀ u, SetsLocal s x v u → Ok u q Q) : Ok s (.seq (callTo x f [a1, a2, a3]) q) Q := by
  rcases call3_ret s x f x1 x2 x3 body a1 a2 a3 v1 v2 v3 v w0 h12 h13 h23 hcode ha1 ha2 ha3 hx hbody with
    hs | ⟨u, hu, m, d, g, c, b, lx, lo⟩
  · exact Or.inl (seq_stop s _ _ hs)
  · exact ok_seq hu (k u ⟨m, d, g, c, b, lx, lo⟩)

end

def sM := ofString "m"
def sR := ofString "res"
def fNth := ofString "natListNth"

def nnSent : Nat := 2 ^ 63

/-- The answer: the `k`-th element, capped, or the sentinel. -/
def nnRes (us : List Nat) (k : Nat) : BitVec 64 :=
  if h : k < us.length then BitVec.ofNat 64 (min us[k] natCap) else BitVec.ofNat 64 nnSent

def nnBody : ProgHOL 64 :=
  .seq (bAt sC (vv sHP))
  (.ite digitTest
    (.seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sHP])
    (.ite (.cmp .equal (vv sE2) (vv sHP)) hang
    (.ite (.cmp .equal (vv sM) (vv sL))
      (.seq (callTo sR fReadNat [vv sB, vv sHP, vv sE2]) (.assign .local sG (.const 0)))
      (.seq (callTo sHP fSkipWs [vv sB, vv sN, vv sE2])
      (.seq (bAt sC (vv sHP))
      (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 44)))
        (.seq (callTo sHP fSkipWs [vv sB, vv sN, .op .add [vv sHP, .const 1]])
          (.assign .local sM (.op .add [vv sM, .const 1])))
        (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 93)))
          (.seq (.assign .local sR (.const (BitVec.ofNat 64 nnSent))) (.assign .local sG (.const 0)))
          hang)))))))
    hang)

section
variable {σ : Type}

def NnCodes (t : PanSemStateFiniteExact 64 σ) : Prop :=
  SkipWsCode t ∧ SkipDigitsCode t ∧ NumEndCode t ∧
  t.code.lookup fReadNat = some ([(sB, .one), (sI, .one), (sE, .one)], rnFun, .one)

theorem NnCodes.congr {t u : PanSemStateFiniteExact 64 σ} (h : NnCodes t) (hc : u.code = t.code) : NnCodes u := by
  unfold NnCodes SkipWsCode SkipDigitsCode NumEndCode at *
  rw [hc]; exact h

def NnI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (us : List Nat) (e0 : USize) (k : Nat)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧ u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) ∧
  u.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 k))) ∧
  (∃ w, u.locals.lookup sC = some (.val (.word w))) ∧ (∃ w, u.locals.lookup sE2 = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sR = some (.val (.word w))) ∧
  ∃ (j : USize) (acc : List Nat), j.toNat ≤ b.size ∧ acc.length ≤ k ∧
    u.locals.lookup sHP = some (.val (.word (BitVec.ofNat 64 j.toNat))) ∧
    u.locals.lookup sM = some (.val (.word (BitVec.ofNat 64 acc.length))) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ scanNatListLoop b j acc true = .ok us e0) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ u.locals.lookup sR = some (.val (.word (nnRes us k)))))

theorem prefix_get {acc us : List Nat} {x : Nat} (h : (x :: acc).reverse <+: us) :
    ∃ hl : acc.length < us.length, us[acc.length] = x := by
  have hl : acc.length < us.length := by have := h.length_le; simp at this; omega
  refine ⟨hl, ?_⟩
  obtain ⟨r, hr⟩ := h
  have := congrArg (fun l => l[acc.length]?) hr
  simp only [List.reverse_cons] at this
  rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)] at this
  simp at this
  rw [List.getElem?_eq_getElem hl] at this
  exact (Option.some.inj this).symm

end

section
variable {σ : Type}

theorem nn_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : NnCodes t) (us : List Nat) (e0 : USize) (k : Nat) (hk : k < 2 ^ 62)
    (u : PanSemStateFiniteExact 64 σ) (hu : NnI t A b us e0 k u) (hg : u.locals.lookup sG = some (.val (.word 1))) :
    Ok (decClockHOLFinite u) nnBody (NnI t A b us e0 k) := by
  obtain ⟨m0, d0, c0, g0, b0, lb, ln, lk0, ⟨wc, lc⟩, ⟨we, le⟩, ⟨wr, lr⟩, j, acc, hj, hak, lj, lm, br⟩ := hu
  obtain ⟨_, hR⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  let v := decClockHOLFinite u
  have hcv : NnCodes v := hc.congr c0
  have hbv : BytesAt v A b.data.toList := bytesAt_congr hb m0 d0 b0
  unfold nnBody
  have e1 := bAt_spec v A b.data.toList sC (vv sHP) j.toNat hbv (by omega) wc (by lk [v]; exact lc)
    (by lk [v]; exact lb) (by lk [v]; simpa using ln) (eval_vv v sHP _ (by lk [v]; exact lj))
  refine ok_seq e1 ?_
  let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList j.toNat).toNat))) v
  have L1 : ∀ y, y ≠ sC → v1.locals.lookup y = u.locals.lookup y := fun y h => by
    simp only [v1, v]; rw [lookup_setVar_other _ _ h]; rfl
  refine ok_ite (digitTest_ok v1 (byteL b.data.toList j.toNat).toNat (UInt8.toNat_lt _) (by lk [v1]))
    (fun hw => ?_) (fun _ => ok_hang _ _)
  have hd : isDigitN (byteL b.data.toList j.toNat).toNat = true := by
    by_cases h : isDigitN (byteL b.data.toList j.toNat).toNat = true
    · exact h
    · simp [bw, h] at hw
  have hjl : j.toNat < b.size := by have := lt_of_digit hd; simpa using this
  have hdA : isDigit (byteAt b j) = true := by rw [isDigit_eq, byteAt_eq hp j]; simpa [byteL] using hd
  -- numEnd
  obtain ⟨e, hed⟩ : ∃ x, x = numEnd b j := ⟨_, rfl⟩
  have heL := numEnd_eq hp j hj
  rw [← hed] at heL
  have hele : e.toNat ≤ b.size := by
    have := numEndL_le b.data.toList j.toNat (by simpa using hj)
    rw [heL]; simpa using this
  have hje : j.toNat ≤ e.toNat := by rw [heL]; exact numEndL_ge _ _
  refine ok_call3 (v := BitVec.ofNat 64 e.toNat) (w0 := we) (by decide) (by decide) (by decide) hcv.2.2.1
    (eval_vv v1 sB _ (by rw [L1 _ (by decide)]; exact lb)) (eval_vv v1 sN _ (by rw [L1 _ (by decide)]; exact ln))
    (eval_vv v1 sHP _ (by rw [L1 _ (by decide)]; exact lj)) (by rw [L1 _ (by decide)]; exact le)
    (fun callee h1 h2 h3 => by
      rw [hed]; exact numEnd_refines (callEntryStateHOLFinite v1 callee) A b hp (bytesAt_congr hbv rfl rfl rfl)
        j hj hcv.2.1 h1 h2 h3) (fun u1 hs1 => ?_)
  obtain ⟨m1, d1, g1, c1, b1, le1, lo1⟩ := hs1
  have L2 : ∀ y, y ≠ sE2 → y ≠ sC → u1.locals.lookup y = u.locals.lookup y := fun y h h' => by
    rw [lo1 y h, L1 y h']
  have hcmp := ConsLoop.eval_cmp_of u1 .equal (vv sE2) (vv sHP) _ _ (eval_vv u1 sE2 _ le1)
    (eval_vv u1 sHP _ (by rw [L2 _ (by decide) (by decide)]; exact lj))
  rw [bw_eq _ _ (usz_lt e) (usz_lt j)] at hcmp
  refine ok_ite hcmp (fun _ => ok_hang _ _) (fun hw => ?_)
  have hej : e.toNat ≠ j.toNat := by intro h; simp [bw, h] at hw
  have hje' : j.toNat < e.toNat := by omega
  have hdig := nlLoop_digit (acc := acc) ((hp.lt_iff j).mpr hjl) _ rfl hdA hed.symm (fun h => hej (by rw [h]))
    (USize.lt_iff_toNat_lt.mpr hje')
  rw [hdig] at hR
  obtain ⟨hal, hux⟩ := prefix_get (nlLoop_prefix b _ _ _ _ _ _ rfl hR)
  have hcmpk := ConsLoop.eval_cmp_of u1 .equal (vv sM) (vv sL) _ _
    (eval_vv u1 sM _ (by rw [L2 _ (by decide) (by decide)]; exact lm))
    (eval_vv u1 sL _ (by rw [L2 _ (by decide) (by decide)]; exact lk0))
  rw [bw_eq _ _ (by omega) (by omega)] at hcmpk
  have hcu1 : NnCodes u1 := hcv.congr c1
  have hbu1 : BytesAt u1 A b.data.toList := bytesAt_congr hbv m1 d1 b1
  refine ok_ite hcmpk (fun hw => ?_) (fun hw => ?_)
  · -- found: the k-th element
    have hak' : acc.length = k := by
      by_cases h : acc.length = k
      · exact h
      · simp [bw, h] at hw
    have hsk : e.toNat = skipDigitsL b.data.toList j.toNat := by
      rw [heL]; exact numEndL_skip _ _ (by rw [← heL]; exact hej)
    refine ok_call3 (v := BitVec.ofNat 64 (min (readNatAt b j e) natCap)) (w0 := wr) (by decide) (by decide)
      (by decide) hcu1.2.2.2 (eval_vv u1 sB _ (by rw [L2 _ (by decide) (by decide)]; exact lb))
      (eval_vv u1 sHP _ (by rw [L2 _ (by decide) (by decide)]; exact lj)) (eval_vv u1 sE2 _ le1)
      (by rw [L2 _ (by decide) (by decide)]; exact lr)
      (fun callee h1 h2 h3 => rnFun_refines (callEntryStateHOLFinite u1 callee) A b hp
        (bytesAt_congr hbu1 rfl rfl rfl) j e hj hsk h1 h3 h2) (fun u2 hs2 => ?_)
    obtain ⟨m2, d2, g2, c2, b2, lr2, lo2⟩ := hs2
    have L3 : ∀ y, y ≠ sR → y ≠ sE2 → y ≠ sC → u2.locals.lookup y = u.locals.lookup y := fun y h h' h'' => by
      rw [lo2 y h, L2 y h' h'']
    refine ok_assign (v := 0) (by simp [evalHOLExact]) (by rw [L3 _ (by decide) (by decide) (by decide)]; exact hg) ?_
    refine ⟨m2.trans (m1.trans m0), d2.trans (d1.trans d0), c2.trans (c1.trans c0), g2.trans (g1.trans g0),
      b2.trans (b1.trans b0), by lk; rw [L3 _ (by decide) (by decide) (by decide)]; exact lb,
      by lk; rw [L3 _ (by decide) (by decide) (by decide)]; exact ln,
      by lk; rw [L3 _ (by decide) (by decide) (by decide)]; exact lk0,
      ⟨_, by lk; rw [lo2 _ (by decide), lo1 _ (by decide)]; lk [v1] <;> rfl⟩, ⟨_, by lk; rw [lo2 _ (by decide)]; exact le1⟩,
      ⟨_, by lk; exact lr2⟩, j, acc, hj, hak, by lk; rw [L3 _ (by decide) (by decide) (by decide)]; exact lj,
      by lk; rw [L3 _ (by decide) (by decide) (by decide)]; exact lm, Or.inr ⟨by lk, ?_⟩⟩
    lk; rw [lr2]
    unfold nnRes
    rw [dite_eq_left (by omega)]
    congr 4
    subst hak'; rw [hux]
  · -- not yet: past the separator
    have hak' : acc.length < k := by
      have : acc.length ≠ k := by intro h; simp [bw, h] at hw
      omega
    obtain ⟨q, hqd⟩ : ∃ x, x = skipWs b e := ⟨_, rfl⟩
    have hqL := skipWs_eq hp _ e rfl
    rw [← hqd] at hqL
    have hqle : q.toNat ≤ b.size := by
      have := skipL_le_length isWsN b.data.toList _ e.toNat rfl (by simpa using hele)
      rw [hqL]; simpa using this
    refine ok_call3 (v := BitVec.ofNat 64 q.toNat) (w0 := BitVec.ofNat 64 j.toNat) (by decide) (by decide)
      (by decide) hcu1.1 (eval_vv u1 sB _ (by rw [L2 _ (by decide) (by decide)]; exact lb))
      (eval_vv u1 sN _ (by rw [L2 _ (by decide) (by decide)]; exact ln)) (eval_vv u1 sE2 _ le1)
      (by rw [L2 _ (by decide) (by decide)]; exact lj)
      (fun callee h1 h2 h3 => by
        rw [hqd]; exact skipWs_refines (callEntryStateHOLFinite u1 callee) A b hp
          (bytesAt_congr hbu1 rfl rfl rfl) e hele h1 h2 h3) (fun u2 hs2 => ?_)
    obtain ⟨m2, d2, g2, c2, b2, lq2, lo2⟩ := hs2
    have L3 : ∀ y, y ≠ sHP → y ≠ sE2 → y ≠ sC → u2.locals.lookup y = u.locals.lookup y := fun y h h' h'' => by
      rw [lo2 y h, L2 y h' h'']
    have hbu2 : BytesAt u2 A b.data.toList := bytesAt_congr hbu1 m2 d2 b2
    have e3 := bAt_spec u2 A b.data.toList sC (vv sHP) q.toNat hbu2 (by omega)
      (BitVec.ofNat 64 (byteL b.data.toList j.toNat).toNat) (by rw [lo2 _ (by decide), lo1 _ (by decide)]; lk [v1])
      (by rw [L3 _ (by decide) (by decide) (by decide)]; exact lb)
      (by rw [L3 _ (by decide) (by decide) (by decide)]; simpa using ln) (eval_vv u2 sHP _ lq2)
    refine ok_seq e3 ?_
    let u3 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList q.toNat).toNat))) u2
    have L4 : ∀ y, y ≠ sHP → y ≠ sE2 → y ≠ sC → u3.locals.lookup y = u.locals.lookup y := fun y h h' h'' => by
      simp only [u3]; rw [lookup_setVar_other _ _ h'', L3 y h h' h'']
    have hcq := UInt8.toNat_lt (byteL b.data.toList q.toNat)
    have hws1 := nlLoop_ws b _ e (ConLeche.Frontend.readNatAt b j e :: acc) false rfl
    rw [← hqd] at hws1
    refine ok_ite (eval_eq_c u3 sC (byteL b.data.toList q.toNat).toNat 44 (by omega) (by decide) (by lk [u3]))
      (fun hw => ?_) (fun hw0 => ?_)
    · have h44 : (byteL b.data.toList q.toNat).toNat = 44 := by
        by_cases h : (byteL b.data.toList q.toNat).toNat = 44
        · exact h
        · simp [bw, h] at hw
      have hql : q.toNat < b.size := by have := lt_of_byteL h44 (by decide); simpa using this
      have hq1 : (q + 1).toNat = q.toNat + 1 := ConLeche.Frontend.usizeStep b q ((hp.lt_iff q).mpr hql)
      have hb44 : byteAt b q = 44 := byteAt_of_byteL hp q 44 (by decide) h44
      obtain ⟨j', hjd⟩ : ∃ x, x = skipWs b (q + 1) := ⟨_, rfl⟩
      have hjL := skipWs_eq hp _ (q + 1) rfl
      rw [← hjd, hq1] at hjL
      have hjle : j'.toNat ≤ b.size := by
        have := skipL_le_length isWsN b.data.toList _ (q.toNat + 1) rfl (by simp; omega)
        rw [hjL]; simpa using this
      refine ok_call3 (v := BitVec.ofNat 64 j'.toNat) (v3 := BitVec.ofNat 64 (q + 1).toNat)
        (w0 := BitVec.ofNat 64 q.toNat) (by decide) (by decide)
        (by decide) (hcu1.congr c2).1
        (eval_vv u3 sB _ (by rw [L4 _ (by decide) (by decide) (by decide)]; exact lb))
        (eval_vv u3 sN _ (by rw [L4 _ (by decide) (by decide) (by decide)]; exact ln))
        (by rw [eval_add_c u3 sHP _ _ (by lk [u3]; exact lq2), hq1]; congr 3; apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_add]; try omega)
        (by lk [u3]; exact lq2)
        (fun callee h1 h2 h3 => by
          rw [hjd]; exact skipWs_refines (callEntryStateHOLFinite u3 callee) A b hp
            (bytesAt_congr hbu2 rfl rfl rfl) (q + 1) (by omega) h1 h2 h3) (fun u4 hs4 => ?_)
      obtain ⟨m4, d4, g4, c4, b4, lj4, lo4⟩ := hs4
      have lm4 : u4.locals.lookup sM = some (.val (.word (BitVec.ofNat 64 acc.length))) := by
        rw [lo4 _ (by decide), L4 _ (by decide) (by decide) (by decide)]; exact lm
      refine ok_assign (v := BitVec.ofNat 64 (acc.length + 1)) (by
        rw [eval_add_c u4 sM _ _ lm4]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) lm4 ?_
      have L5 : ∀ y, y ≠ sM → y ≠ sHP → y ≠ sE2 → y ≠ sC →
          (setVarHOLFinite sM (.val (.word (BitVec.ofNat 64 (acc.length + 1)))) u4).locals.lookup y =
            u.locals.lookup y := fun y h0 h h' h'' => by
        rw [lookup_setVar_other _ _ h0, lo4 y h, L4 y h h' h'']
      refine ⟨m4.trans (m2.trans (m1.trans m0)), d4.trans (d2.trans (d1.trans d0)),
        c4.trans (c2.trans (c1.trans c0)), g4.trans (g2.trans (g1.trans g0)), b4.trans (b2.trans (b1.trans b0)),
        by rw [L5 _ (by decide) (by decide) (by decide) (by decide)]; exact lb,
        by rw [L5 _ (by decide) (by decide) (by decide) (by decide)]; exact ln,
        by rw [L5 _ (by decide) (by decide) (by decide) (by decide)]; exact lk0,
        ⟨_, by rw [lookup_setVar_other _ _ (by decide), lo4 _ (by decide)]; lk [u3] <;> rfl⟩,
        ⟨_, by rw [lookup_setVar_other _ _ (by decide), lo4 _ (by decide)]; lk [u3]; rw [lo2 _ (by decide)]; exact le1⟩,
        ⟨_, by rw [L5 _ (by decide) (by decide) (by decide) (by decide)]; exact lr⟩,
        j', ConLeche.Frontend.readNatAt b j e :: acc, hjle, by simp; omega,
        by rw [lookup_setVar_other _ _ (by decide)]; exact lj4, by rw [lookup_setVar_same]; simp,
        Or.inl ⟨by rw [L5 _ (by decide) (by decide) (by decide) (by decide)]; exact hg, ?_⟩⟩
      rw [← hR, hws1, nlLoop_comma ((hp.lt_iff q).mpr hql) hb44, nlLoop_ws b _ (q + 1) _ true rfl, ← hjd]
    · have hn44 : (byteL b.data.toList q.toNat).toNat ≠ 44 := by intro h; simp [bw, h] at hw0
      refine ok_ite (eval_eq_c u3 sC (byteL b.data.toList q.toNat).toNat 93 (by omega) (by decide) (by lk [u3]))
        (fun hw => ?_) (fun _ => ok_hang _ _)
      have h93 : (byteL b.data.toList q.toNat).toNat = 93 := by
        by_cases h : (byteL b.data.toList q.toNat).toNat = 93
        · exact h
        · simp [bw, h] at hw
      have hql : q.toNat < b.size := by have := lt_of_byteL h93 (by decide); simpa using this
      have hb93 : byteAt b q = 93 := byteAt_of_byteL hp q 93 (by decide) h93
      rw [hws1, nlLoop_close ((hp.lt_iff q).mpr hql) hb93] at hR
      simp only [ScanRes.ok.injEq] at hR
      have hus : us = (ConLeche.Frontend.readNatAt b j e :: acc).reverse := hR.1.symm
      have lr3 : u3.locals.lookup sR = some (.val (.word wr)) := by
        rw [L4 _ (by decide) (by decide) (by decide)]; exact lr
      refine ok_seq (ConsLoop.assign_local u3 sR _ (BitVec.ofNat 64 nnSent) wr (by simp [evalHOLExact]) lr3) ?_
      let u5 := setVarHOLFinite sR (.val (.word (BitVec.ofNat 64 nnSent))) u3
      refine ok_assign (v := 0) (by simp [evalHOLExact]) (by lk [u5]; rw [L4 _ (by decide) (by decide) (by decide)]; exact hg) ?_
      refine ⟨m2.trans (m1.trans m0), d2.trans (d1.trans d0), c2.trans (c1.trans c0), g2.trans (g1.trans g0),
        b2.trans (b1.trans b0), by lk [u5]; rw [L4 _ (by decide) (by decide) (by decide)]; exact lb,
        by lk [u5]; rw [L4 _ (by decide) (by decide) (by decide)]; exact ln,
        by lk [u5]; rw [L4 _ (by decide) (by decide) (by decide)]; exact lk0,
        ⟨_, by lk [u5, u3] <;> rfl⟩, ⟨_, by lk [u5, u3]; rw [lo2 _ (by decide)]; exact le1⟩, ⟨_, by lk [u5] <;> rfl⟩,
        q, acc, hqle, hak, by lk [u5, u3]; exact lq2, by lk [u5]; rw [L4 _ (by decide) (by decide) (by decide)]; exact lm,
        Or.inr ⟨by lk, ?_⟩⟩
      lk [u5]
      unfold nnRes
      rw [dite_eq_right (by rw [hus]; simp; omega)]
end

def nnFun : ProgHOL 64 :=
  .dec sC .one (.const 0) (.dec sE2 .one (.const 0) (.dec sHP .one (.const 0) (.dec sM .one (.const 0)
  (.dec sR .one (.const 0) (.dec sG .one (.const 1)
  (.seq (bAt sC (vv sI))
  (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 91)))
    (.seq (callTo sHP fSkipWs [vv sB, vv sN, .op .add [vv sI, .const 1]])
    (.seq (bAt sC (vv sHP))
    (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 93))) (.return (.const (BitVec.ofNat 64 nnSent)))
      (.seq (.while (vv sG) nnBody) (.return (vv sR))))))
    hang)))))))

section
variable {σ : Type}

theorem nnLoop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : NnCodes t) (us : List Nat) (e0 : USize) (k : Nat) (hk : k < 2 ^ 62)
    (u : PanSemStateFiniteExact 64 σ) (hu : NnI t A b us e0 k u) :
    Stop (evaluateHOLFiniteState u (.while (vv sG) nnBody)).1 ∨
      ((evaluateHOLFiniteState u (.while (vv sG) nnBody)).1 = none ∧
        NnI t A b us e0 k (evaluateHOLFiniteState u (.while (vv sG) nnBody)).2 ∧
        (evaluateHOLFiniteState u (.while (vv sG) nnBody)).2.locals.lookup sR = some (.val (.word (nnRes us k)))) := by
  have := while_stop (vv sG) nnBody (NnI t A b us e0 k)
    (fun u => NnI t A b us e0 k u ∧ u.locals.lookup sR = some (.val (.word (nnRes us k))))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, j, acc, _, _, _, _, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, hr⟩
      · exact ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide),
          fun _ _ => nn_step t A b hp hb hc us e0 k hk u hu hg⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, hr⟩, fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

/-- **The `k`-th element of a number list in Pancake is con-leche's** (capped), or the sentinel when
the list is shorter. -/
theorem nnFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : NnCodes t) (v : USize) (hv : v.toNat ≤ b.size) (k : Nat)
    (hk : k < 2 ^ 62) (us : List Nat) (e0 : USize) (hs : scanNatList b v = .ok us e0)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 k)))) :
    RetP t nnFun (fun w => w = nnRes us k) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  unfold nnFun
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 1) (by simp [evalHOLExact]) ?_
  let t2 := setVarHOLFinite sG (.val (.word 1)) (setVarHOLFinite sR (.val (.word 0))
    (setVarHOLFinite sM (.val (.word 0)) (setVarHOLFinite sHP (.val (.word 0))
      (setVarHOLFinite sE2 (.val (.word 0)) (setVarHOLFinite sC (.val (.word 0)) t)))))
  have e1 := bAt_spec t2 A b.data.toList sC (vv sI) v.toNat (bytesAt_congr hb rfl rfl rfl) (by omega) 0
    (by lk [t2]) (by lk [t2]; exact lb) (by lk [t2]; simpa using ln) (eval_vv t2 sI _ (by lk [t2]; exact li))
  refine retP_seq e1 ?_ rfl rfl rfl rfl rfl
  let t3 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat))) t2
  refine retP_ite (eval_eq_c t3 sC (byteL b.data.toList v.toNat).toNat 91
    (by have := UInt8.toNat_lt (byteL b.data.toList v.toNat); omega) (by decide) (by lk [t3]))
    (fun hw => ?_) (fun _ => retP_hang _ _)
  have hq : (byteL b.data.toList v.toNat).toNat = 91 := by
    by_cases h : (byteL b.data.toList v.toNat).toNat = 91
    · exact h
    · simp [bw, h] at hw
  have hvl : v.toNat < b.size := by have := lt_of_byteL hq (by decide); simpa using this
  have hv1 : (v + 1).toNat = v.toNat + 1 := ConLeche.Frontend.usizeStep b v ((hp.lt_iff v).mpr hvl)
  have hb91 : byteAt b v = 91 := byteAt_of_byteL hp v 91 (by decide) hq
  have hs' : scanNatListLoop b (v + 1) [] true = .ok us e0 := by
    rw [scanNatList, ite_eq_left (by rw [hb91]; rfl)] at hs; exact hs
  obtain ⟨j, hjd⟩ : ∃ x, x = skipWs b (v + 1) := ⟨_, rfl⟩
  have hjL := skipWs_eq hp _ (v + 1) rfl
  rw [← hjd, hv1] at hjL
  have hjle : j.toNat ≤ b.size := by
    have := skipL_le_length isWsN b.data.toList _ (v.toNat + 1) rfl (by simp; omega)
    rw [hjL]; simpa using this
  rw [nlLoop_ws b _ (v + 1) [] true rfl, ← hjd] at hs'
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 (v + 1).toNat)
    (v := BitVec.ofNat 64 j.toNat) (w0 := 0) (by decide) (by decide) (by decide) hc.1
    (eval_vv t3 sB _ (by lk [t3, t2]; exact lb)) (eval_vv t3 sN _ (by lk [t3, t2]; exact ln))
    (by rw [eval_add_c t3 sI _ _ (by lk [t3, t2]; exact li), hv1]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega)
    (by lk [t3, t2]) (fun callee h1 h2 h3 => by
      rw [hjd]; exact skipWs_refines (callEntryStateHOLFinite t3 callee) A b hp (bytesAt_congr hb rfl rfl rfl)
        (v + 1) (by omega) h1 h2 h3) (fun u1 hs1 => ?_)
  obtain ⟨m1, d1, g1, c1, b1, lj1, lo1⟩ := hs1
  have hbu1 : BytesAt u1 A b.data.toList := bytesAt_congr hb m1 d1 b1
  have e2 := bAt_spec u1 A b.data.toList sC (vv sHP) j.toNat hbu1 (by omega)
    (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat) (by rw [lo1 _ (by decide)]; lk [t3])
    (by rw [lo1 _ (by decide)]; lk [t3, t2]; exact lb) (by rw [lo1 _ (by decide)]; lk [t3, t2]; simpa using ln)
    (eval_vv u1 sHP _ lj1)
  refine retP_seq e2 ?_ rfl rfl rfl rfl rfl
  let u2 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList j.toNat).toNat))) u1
  refine retP_ite (eval_eq_c u2 sC (byteL b.data.toList j.toNat).toNat 93
    (by have := UInt8.toNat_lt (byteL b.data.toList j.toNat); omega) (by decide) (by lk [u2]))
    (fun hw => ?_) (fun hw0 => ?_)
  · -- the empty list
    have h93 : (byteL b.data.toList j.toNat).toNat = 93 := by
      by_cases h : (byteL b.data.toList j.toNat).toNat = 93
      · exact h
      · simp [bw, h] at hw
    have hjl : j.toNat < b.size := by have := lt_of_byteL h93 (by decide); simpa using this
    rw [nlLoop_close0 ((hp.lt_iff j).mpr hjl) (byteAt_of_byteL hp j 93 (by decide) h93)] at hs'
    simp only [ScanRes.ok.injEq] at hs'
    obtain ⟨rfl, -⟩ := hs'
    unfold RetP
    rw [evaluateHOLFiniteState_eq_evaluate_def u2 (.return _)]
    refine Or.inr ⟨BitVec.ofNat 64 nnSent, ?_, by simp [nnRes], ?_⟩
    · simp [evalHOLExact, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL]
    · simp [evalHOLExact, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
        emptyLocalsHOLFinite] <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · -- the loop
    have h0 : NnI u2 A b us e0 k u2 :=
      ⟨rfl, rfl, rfl, rfl, rfl, by lk [u2]; rw [lo1 _ (by decide)]; lk [t3, t2]; exact lb,
        by lk [u2]; rw [lo1 _ (by decide)]; lk [t3, t2]; exact ln,
        by lk [u2]; rw [lo1 _ (by decide)]; lk [t3, t2]; exact ll,
        ⟨_, by lk [u2] <;> rfl⟩, ⟨_, by lk [u2]; rw [lo1 _ (by decide)]; lk [t3, t2] <;> rfl⟩,
        ⟨_, by lk [u2]; rw [lo1 _ (by decide)]; lk [t3, t2] <;> rfl⟩,
        j, [], hjle, by simp, by lk [u2]; exact lj1, by lk [u2]; rw [lo1 _ (by decide)]; lk [t3, t2]; rfl,
        Or.inl ⟨by lk [u2]; rw [lo1 _ (by decide)]; lk [t3, t2], hs'⟩⟩
    rcases nnLoop_spec u2 A b hp (bytesAt_congr hbu1 rfl rfl rfl) (hc.congr (by rw [show u2.code = u1.code from rfl, c1]; rfl))
        us e0 k hk u2 h0 with hs | ⟨hn, hI, hres⟩
    · exact Or.inl (seq_stop u2 _ _ hs)
    · obtain ⟨m0, d0, c0, g0, b0, -⟩ := hI
      generalize hu : evaluateHOLFiniteState u2 (.while (vv sG) nnBody) = r at hn hres m0 d0 c0 g0 b0
      obtain ⟨r1, r2⟩ := r
      simp only at hn hres m0 d0 c0 g0 b0
      subst hn
      unfold RetP
      rw [seq_normal _ hu]
      obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv r2 sR _ hres
      exact Or.inr ⟨_, q1, rfl, q2.trans m0, q3.trans d0, q4.trans g0, q5.trans c0, q6.trans b0⟩

end

end ConPanqueque.Scan
