import ConPanqueque.V.NIntern
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Expression interns with variable-length keys

`eRestE_spec`: the expression remainder (`rRestE` at an expression kind, flag `fle`) with the result
in `ERes` form. `bvar i`: key `limbs i` placed by the caller, derived `bvarDataE` of the low word.
(`fvar`, `lit`, `proj` follow.)
-/

namespace ConPanqueque.V

section
variable {σ : Type}

theorem erep_bvars {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl BVarNode EIdx UInt64)
    (hP : TabAt u L 9 0 Enc.encBVar dWN P' (mkN ETag.bvar 0)) (hS : TabAt u L 9 1 Enc.encBVar dWN Sc' (mkN ETag.bvar 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 9 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with bvars := P' }, scr := { st.scr with bvars := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 9 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    hP,
    A 10 0 (by decide) (by decide) (by decide) (by decide) h.p1,
    A 11 0 (by decide) (by decide) (by decide) (by decide) h.p2,
    A 12 0 (by decide) (by decide) (by decide) (by decide) h.p3,
    A 13 0 (by decide) (by decide) (by decide) (by decide) h.p4,
    A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6,
    A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8,
    A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    hS,
    A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2,
    A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4,
    A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6,
    A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8,
    A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

theorem erep_fvars {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl FVarNode EIdx UInt64)
    (hP : TabAt u L 10 0 Enc.encFVar dWN P' (mkN ETag.fvar 0)) (hS : TabAt u L 10 1 Enc.encFVar dWN Sc' (mkN ETag.fvar 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 10 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with fvars := P' }, scr := { st.scr with fvars := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 10 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) (by decide) h.p0,
    hP,
    A 11 0 (by decide) (by decide) (by decide) (by decide) h.p2,
    A 12 0 (by decide) (by decide) (by decide) (by decide) h.p3,
    A 13 0 (by decide) (by decide) (by decide) (by decide) h.p4,
    A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6,
    A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8,
    A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0,
    hS,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2,
    A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4,
    A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6,
    A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8,
    A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

theorem erep_lits {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl LitNode EIdx UInt64)
    (hP : TabAt u L 17 0 Enc.encLit dWN P' (mkN ETag.lit 0)) (hS : TabAt u L 17 1 Enc.encLit dWN Sc' (mkN ETag.lit 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 17 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with lits := P' }, scr := { st.scr with lits := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 17 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) (by decide) h.p0,
    A 10 0 (by decide) (by decide) (by decide) (by decide) h.p1,
    A 11 0 (by decide) (by decide) (by decide) (by decide) h.p2,
    A 12 0 (by decide) (by decide) (by decide) (by decide) h.p3,
    A 13 0 (by decide) (by decide) (by decide) (by decide) h.p4,
    A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6,
    A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    hP,
    A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0,
    A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2,
    A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4,
    A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6,
    A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    hS,
    A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

theorem erep_projs {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl ProjNode EIdx UInt64)
    (hP : TabAt u L 18 0 Enc.encProj dWN P' (mkN ETag.proj 0)) (hS : TabAt u L 18 1 Enc.encProj dWN Sc' (mkN ETag.proj 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 18 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with projs := P' }, scr := { st.scr with projs := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 18 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) (by decide) h.p0,
    A 10 0 (by decide) (by decide) (by decide) (by decide) h.p1,
    A 11 0 (by decide) (by decide) (by decide) (by decide) h.p2,
    A 12 0 (by decide) (by decide) (by decide) (by decide) h.p3,
    A 13 0 (by decide) (by decide) (by decide) (by decide) h.p4,
    A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6,
    A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8,
    hP,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0,
    A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    A 11 1 (by decide) (by decide) (by decide) (by decide) h.s2,
    A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4,
    A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6,
    A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8,
    hS⟩

end

section
variable {σ : Type} {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

theorem eRestE_spec (t u : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (w k : Nat)
    (lenE : ExpHOL 64) (st : EStore) (enc : α → List (BitVec 64)) (hinj : ∀ x y, enc x = enc y → x = y)
    (mkP mkS : Nat → EIdx) (icap : Nat)
    (hmkP : ∀ i, i < icap → Enc.idxW (mkP i) = L.base k 0 + BitVec.ofNat 64 i)
    (hmkS : ∀ i, i < icap → Enc.idxW (mkS i) = L.base k 1 + BitVec.ofNat 64 i)
    (hicap : ∀ tier, tier < 2 → (L.geo k tier).cap ≤ icap)
    (P Sc : Tbl α EIdx UInt64) (sk : Bool) (x : α) (d : UInt64) (res : EStore × EIdx)
    (setK : Tbl α EIdx UInt64 → Tbl α EIdx UInt64 → EStore)
    (hres : res = (setK (twoTier P Sc st.scratchOn sk x d mkP mkS).1 (twoTier P Sc st.scratchOn sk x d mkP mkS).2.1,
      (twoTier P Sc st.scratchOn sk x d mkP mkS).2.2))
    (hlss : ∀ P' S', (setK P' S').lss = st.lss)
    (hset : ∀ (v v' : PanSemStateFiniteExact 64 σ) P' S', ERep v L FLe st → TabAt v' L k 0 enc dWN P' mkP →
      TabAt v' L k 1 enc dWN S' mkS → v'.memory FLe = v.memory FLe → v'.memaddrs = v.memaddrs →
      (∀ k' tier, 9 ≤ k' → k' < 19 → tier < 2 → k' ≠ k → Agree L FLe v v' k' tier) → ERep v' L FLe (setK P' S'))
    (hS : SepK L FLn FLl FLs FLe KB w k) (hk : 9 ≤ k) (hk19 : k < 19) (hwl : (enc x).length = w) (hw : w < 2 ^ 61)
    (hR : SRep u L FLn FLl FLs FLe st)
    (hPa : TabAt u L k 0 enc dWN P mkP) (hSa : TabAt u L k 1 enc dWN Sc mkS)
    (hK : Words u KB (enc x))
    (hm : ∀ c, (∀ j, j < w → c ≠ KB + BitVec.ofNat 64 (8 * j)) → u.memory c = t.memory c)
    (hd : u.memaddrs = t.memaddrs) (hc : u.code = t.code) (hg : u.globals = t.globals) (hta : u.topAddr = t.topAddr)
    (ldv : u.locals.lookup lDv = some (.val (.word (dWN d).1)))
    (ldv2 : u.locals.lookup lDv2 = some (.val (.word (dWN d).2)))
    (lsk : u.locals.lookup lSk = some (.val (.word (if sk then 1 else 0))))
    (lfle : u.locals.lookup lFle = some (.val (.word FLe)))
    (ldir : u.locals.lookup lDir = some (.val (.word L.DIR))) (lkb : u.locals.lookup lKb = some (.val (.word KB)))
    (hw5 : ∀ y, y ∈ [lFl, lOn, lPg, lSg, lK, lL] → ∃ w, u.locals.lookup y = some (.val (.word w)))
    (hlen : ∀ x : PanSemStateFiniteExact 64 σ, (∀ y, y ∉ [lFl, lOn, lPg, lSg, lK] → x.locals.lookup y = u.locals.lookup y) →
      @evalHOLExact 64 σ _ x.toExact (fun c => Classical.propDecidable (x.memaddrs c)) lenE =
        some (.val (.word (BitVec.ofNat 64 w)))) :
    ERes t L FLn FLl FLs FLe KB w st res (evaluateHOLFiniteState u (rRestE k lenE lFle)) := by
  have R := rRestE_spec t u L FLn FLl FLs FLe KB FLe w k lFle lenE (by decide) st.scratchOn enc dWN Enc.idxW hinj
    mkP mkS icap hmkP hmkS hicap P Sc sk x d (fun v' => SRep v' L FLn FLl FLs FLe res.1)
    (fun v' hP hS' hf hd' hag => by
      rw [hres]
      exact low_frame hR ⟨hf _ (Or.inl rfl), hf _ (Or.inr (Or.inl rfl)), hf _ (Or.inr (Or.inr (Or.inl rfl)))⟩ hd'
        (fun k' tier h1 h2 => hag k' tier (by omega) h2 (by omega)) _ (hlss _ _)
        (hset u v' _ _ hR.e hP hS' (hf _ (Or.inr (Or.inr (Or.inr rfl)))) hd'
          (fun k' tier _ h2 h3 h4 => hag k' tier h2 h3 h4)))
    hS hk19 hwl hw (Or.inr (Or.inr (Or.inr rfl))) hR.e.fl hPa hSa hK ldv ldv2 lsk lfle ldir lkb hw5 hlen
  rcases R with hs | ⟨hr, hQ, c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  refine Or.inr ⟨by rw [hr, hres], hQ, c3.trans hc, g3.trans hg, d3.trans hd, ta3.trans hta, fun c h1 h2 => ?_⟩
  have n0 : ¬ inR (L.geo k 0) c := fun hc => h1 ⟨k, 0, hk19, by decide, hc⟩
  have n1 : ¬ inR (L.geo k 1) c := fun hc => h1 ⟨k, 1, hk19, by decide, hc⟩
  rw [fr3 c n0 n1]; exact hm c h2

end

def lIw := ofString "iw"

/-- `bvar i`: the caller has put the key `limbs i` at `ekb`, its length in `en`, and `i`'s low word in `iw`. -/
def eBVarWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lDv ExprData.bvarDataE) (.seq (.assign .local lDv2 (.const 0)) (.seq (.assign .local lSk (.const 0)) rest))

def bvarScratch : List MlS := [lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

section
variable {σ : Type}

theorem eInternBVar_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (i : Nat) (hi : i < 2 ^ 63)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encBVar ⟨i⟩).length 9)
    (hK : Words t KB (Enc.encBVar ⟨i⟩)) (hwl : (Enc.encBVar ⟨i⟩).length < 2 ^ 61)
    (hb0 : L.base 9 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.bvar.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 9 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.bvar.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encBVar ⟨i⟩).length))))
    (liw : t.locals.lookup lIw = some (.val (.word (UInt64.ofNat i).toBitVec)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ bvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes t L FLn FLl FLs FLe KB (Enc.encBVar ⟨i⟩).length st (st.intern (.bvar i))
      (evaluateHOLFiniteState t (eBVarWith (rRestE 9 (vv lEn) lFle))) := by
  have W : ∀ y, y ∈ bvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  let dd := st.derOfView (.bvar i)
  have hdd : dd = ExprData.bvarDataW (UInt64.ofNat i) := Der.derOfBVar_eq ra st i hi
  unfold eBVarWith
  obtain ⟨w1, hw1⟩ := W lDv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lDv _ (dWN dd).1 w1
    (by rw [hdd]; exact ExprData.bvarDataE.eval t _ liw) hw1)]
  let t1 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) t
  obtain ⟨w2, hw2⟩ := W lDv2 (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lDv2 (.const 0) (dWN dd).2 w2 (eval_const t1 0) (by lk [t1]; exact hw2))]
  let t2 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) t1
  obtain ⟨w3, hw3⟩ := W lSk (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lSk (.const 0) (if false then 1 else 0) w3 (eval_const t2 0)
    (by lk [t2, t1]; exact hw3))]
  let t3 := setVarHOLFinite lSk (.val (.word (if false then 1 else 0))) t2
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  have hint := estore_bvar st i
  simp only at hint
  exact eRestE_spec t t3 L FLn FLl FLs FLe KB _ 9 (vv lEn) st Enc.encBVar Enc.encBVar_inj (mkN ETag.bvar 0)
    (mkN ETag.bvar 1) (2 ^ 26) (fun i hi => by rw [hb0]; exact idxW_mkN ETag.bvar 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.bvar 1 (by decide) (by decide) i hi) hS.cap
    st.pers.bvars st.scr.bvars false ⟨i⟩ dd _
    (fun P' S' => { st with pers := { st.pers with bvars := P' }, scr := { st.scr with bvars := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_bvars h1 P' S' h2 h3 h4 h5 h6)
    hS (by decide) (by decide) rfl hwl hR3 hR3.e.p0 hR3.e.s0 hK (fun _ _ => rfl) rfl rfl rfl rfl
    (by lk [t3, t2, t1]) (by lk [t3, t2]) (by lk [t3]) (by lk [t3, t2, t1]; exact lfle) (by lk [t3, t2, t1]; exact ldir)
    (by lk [t3, t2, t1]; exact lkb)
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨w, hw⟩ := W lFl (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lOn (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lPg (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lSg (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lK (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩
      · obtain ⟨w, hw⟩ := W lL (by decide); exact ⟨w, by lk [t3, t2, t1]; exact hw⟩)
    (fun x hx => eval_vv x lEn _ (by rw [hx _ (by decide)]; lk [t3, t2, t1]; exact len))

end

end ConPanqueque.V
