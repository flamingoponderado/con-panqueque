import ConPanqueque.V.NIntern
import ConPanqueque.V.ELet
import ConPanqueque.V.NatHash
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena
open ConPanqueque.Hash (leanStringHash leanNatHash natWords)

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

/-- The scratch-child bit of a one-child node, as Pancake computes it. -/
theorem eval_sk1 {σ : Type} {k : IdxKind} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (a : Idx k)
    (ha : s.locals.lookup x = some (.val (.word (Enc.idxW a)))) :
    @evalHOLExact 64 σ _ s.toExact (fun c => Classical.propDecidable (s.memaddrs c))
      (.cmp .notEqual (.shift .lsr (vv x) (.const 31)) (.const 0)) =
      some (.val (.word (if !a.isPersistent then 1 else 0))) := by
  rw [ConsLoop.eval_cmp_of s .notEqual _ _ _ 0 (eval_shr s _ _ _ (eval_vv s x _ ha) (by decide)) (eval_const s 0)]
  simp only [show (31 : BitVec 64).toNat = 31 from rfl]
  have ea := persist_iff a
  by_cases pa : a.isPersistent = true
  · have hb : ((Enc.idxW a >>> (31 : Nat)) == 0) = true := beq_iff_eq.mpr (ea.mp pa)
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb, pa, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  · have h0 : ¬ (Enc.idxW a >>> (31 : Nat) = 0) := fun e => pa (ea.mpr e)
    have hb : ((Enc.idxW a >>> (31 : Nat)) == 0) = false := by simpa using h0
    have pa' : a.isPersistent = false := by simpa using pa
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb, pa', Bool.not_false, ↓reduceIte]

/-- `fvar idx ty`: the caller has put the key `idxW ty :: limbs idx` at `ekb`, its length in `en`, the
type's handle in `ety` and `idx`'s low word in `iw`. -/
def eFVarWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv lEty))
  (.seq (storeDerived 9 10)
  (.seq (.assign .local lDty (vv lDo1))
  (.seq (.assign .local lDv ExprData.fvarDataE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.cmp .notEqual (.shift .lsr (vv lEty) (.const 31)) (.const 0))) rest))))))

def fvarScratch : List MlS := [lDh, lDt, lDg, lDi, lDo1, lDo2, lDty, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

section
variable {σ : Type}

theorem eInternFVar_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (idx : Nat) (ty : EIdx) (hi : idx < 2 ^ 63)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encFVar ⟨idx, ty⟩).length 10)
    (hK : Words t KB (Enc.encFVar ⟨idx, ty⟩)) (hwl : (Enc.encFVar ⟨idx, ty⟩).length < 2 ^ 61)
    (hb0 : L.base 10 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.fvar.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 10 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.fvar.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encFVar ⟨idx, ty⟩).length))))
    (lety : t.locals.lookup lEty = some (.val (.word (Enc.idxW ty))))
    (liw : t.locals.lookup lIw = some (.val (.word (UInt64.ofNat idx).toBitVec)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ fvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes t L FLn FLl FLs FLe KB (Enc.encFVar ⟨idx, ty⟩).length st (st.intern (.fvar idx ty))
      (evaluateHOLFiniteState t (eFVarWith (rRestE 10 (vv lEn) lFle))) := by
  have W : ∀ y, y ∈ fvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  unfold eFVarWith
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lFl _ FLe wf (eval_vv t lFle _ lfle) hwf)]
  let t2 := setVarHOLFinite lFl (.val (.word FLe)) t
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t2 lDh _ (Enc.idxW ty) wh (eval_vv t2 lEty _ (by lk [t2]; exact lety))
    (by lk [t2]; exact hwh))]
  let t3 := setVarHOLFinite lDh (.val (.word (Enc.idxW ty))) t2
  have W3 : ∀ y, y ∈ fvarScratch → y ≠ lFl → y ≠ lDh → ∃ w, t3.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t3, t2]; exact hw⟩
  have hR3 : SRep t3 L FLn FLl FLs FLe st := srep_frame hR ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  have D := eDerived_spec t3 L FLe st hR3.e ty (lookup_setVar_same _ _ _) (by lk [t3, t2]; exact ldir)
    (by lk [t3, t2]) (W3 lDt (by decide) (by decide) (by decide)) (W3 lDg (by decide) (by decide) (by decide))
    (W3 lDi (by decide) (by decide) (by decide)) (W3 lDo1 (by decide) (by decide) (by decide))
    (W3 lDo2 (by decide) (by decide) (by decide))
  obtain ⟨n1, m1', d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D
  generalize hs1 : evaluateHOLFiniteState t3 (storeDerived 9 10) = q1 at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u4⟩ := q1
  simp only at n1 m1' d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  have back : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u4.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t3, t2]
  have wv : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ∈ fvarScratch →
      ∃ w, u4.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back y a1 a2 a3 a4 a5 a6 a7]; exact hw⟩
  let dtd := st.derived ty
  obtain ⟨wdp, hwdp⟩ := wv lDty (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lDty _ _ wdp (eval_vv u4 lDo1 _ o1) hwdp)]
  let u5 := setVarHOLFinite lDty (.val (.word (dWN dtd).1)) u4
  let dd := st.derOfView (.fvar idx ty)
  have hdd : dd = ExprData.fvarDataW (UInt64.ofNat idx) dtd := Der.derOfFVar_eq ra st idx hi ty
  have iw5 : u5.locals.lookup lIw = some (.val (.word (UInt64.ofNat idx).toBitVec)) := by
    lk [u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact liw
  obtain ⟨wv1, hwv1⟩ := wv lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lDv _ (dWN dd).1 wv1
    (by rw [hdd]; exact ExprData.fvarDataE.eval u5 _ dtd iw5 (by show u5.locals.lookup lDty = _; lk [u5]; rfl))
    (by lk [u5]; exact hwv1))]
  let u6 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u5
  obtain ⟨wv2, hwv2⟩ := wv lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u6 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u6 0) (by lk [u6, u5]; exact hwv2))]
  let u7 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u6
  have ety7 : u7.locals.lookup lEty = some (.val (.word (Enc.idxW ty))) := by
    lk [u7, u6, u5]; rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lety
  obtain ⟨wsk, hwsk⟩ := wv lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u7 lSk _ (if EStore.eViewHasScratchChild (.fvar idx ty) then 1 else 0) wsk
    (eval_sk1 u7 lEty ty ety7) (by lk [u7, u6, u5]; exact hwsk))]
  let u8 := setVarHOLFinite lSk (.val (.word (if EStore.eViewHasScratchChild (.fvar idx ty) then 1 else 0))) u7
  have mem8 : u8.memory = t.memory := by show u4.memory = _; rw [m1']; rfl
  have md8 : u8.memaddrs = t.memaddrs := by show u4.memaddrs = _; rw [d1]; rfl
  have hc8 : u8.code = t.code := by show u4.code = _; rw [c1]; rfl
  have hg8 : u8.globals = t.globals := by show u4.globals = _; rw [g1]; rfl
  have ht8 : u8.topAddr = t.topAddr := by show u4.topAddr = _; rw [ta1]; rfl
  have hR8 : SRep u8 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [mem8], by rw [mem8], by rw [mem8], by rw [mem8]⟩ md8
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem8], fun _ _ => by rw [mem8]⟩)
  have g : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDty → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → y ∈ fvarScratch → ∃ w, u8.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 hy
    obtain ⟨w, hw⟩ := wv y a1 a2 a3 a4 a5 a6 a7 hy; exact ⟨w, by lk [u8, u7, u6, u5]; exact hw⟩
  have b8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lDty → y ≠ lDv →
      y ≠ lDv2 → y ≠ lSk → u8.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11; lk [u8, u7, u6, u5]; exact back y a1 a2 a3 a4 a5 a6 a7
  have hint := estore_fvar st idx ty
  simp only at hint
  exact eRestE_spec t u8 L FLn FLl FLs FLe KB _ 10 (vv lEn) st Enc.encFVar Enc.encFVar_inj (mkN ETag.fvar 0)
    (mkN ETag.fvar 1) (2 ^ 26) (fun i hi => by rw [hb0]; exact idxW_mkN ETag.fvar 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.fvar 1 (by decide) (by decide) i hi) hS.cap
    st.pers.fvars st.scr.fvars (EStore.eViewHasScratchChild (.fvar idx ty)) ⟨idx, ty⟩ dd _
    (fun P' S' => { st with pers := { st.pers with fvars := P' }, scr := { st.scr with fvars := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_fvars h1 P' S' h2 h3 h4 h5 h6)
    hS (by decide) (by decide) rfl hwl hR8 hR8.e.p1 hR8.e.s1 (fun j hj => by rw [md8, mem8]; exact hK j hj)
    (fun c _ => by rw [mem8]) md8 hc8 hg8 ht8
    (by lk [u8, u7, u6]) (by lk [u8, u7]) (by lk [u8])
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact lfle)
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact ldir)
    (by rw [b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact lkb)
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨FLe, by lk [u8, u7, u6, u5]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t3, t2]⟩
      · exact g lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact g lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact g lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact g lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact g lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun x hx => eval_vv x lEn _ (by
      rw [hx _ (by decide), b8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; exact len))

end

/-- Moving an `ERes` back over a prefix that changed only locals. -/
theorem eres_back {σ : Type} {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FLn FLl FLs FLe KB : BitVec 64} {w : Nat}
    {st : EStore} {res : EStore × EIdx} {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : ERes u L FLn FLl FLs FLe KB w st res r) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs)
    (hc : u.code = t.code) (hg : u.globals = t.globals) (ht : u.topAddr = t.topAddr) :
    ERes t L FLn FLl FLs FLe KB w st res r := by
  rcases h with hs | ⟨a, b, c, d, e, f, g⟩
  · exact Or.inl hs
  exact Or.inr ⟨a, b, c.trans hc, d.trans hg, e.trans hd, f.trans ht, fun c h1 h2 => by rw [g c h1 h2, hm]⟩

/-- The part of a `lit` intern after the literal's hash (in `h`). -/
def eLitTail (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lDv Der.litDataE) (.seq (.assign .local lDv2 (.const 0)) (.seq (.assign .local lSk (.const 0)) rest))

section
variable {σ : Type}

theorem eLitTail_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (l : ConLeche.Literal)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encLit ⟨l⟩).length 17)
    (hK : Words t KB (Enc.encLit ⟨l⟩)) (hwl : (Enc.encLit ⟨l⟩).length < 2 ^ 61)
    (hb0 : L.base 17 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 17 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encLit ⟨l⟩).length))))
    (lhv : t.locals.lookup lHv = some (.val (.word (ConLeche.Literal.hash l).toBitVec)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ bvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes t L FLn FLl FLs FLe KB (Enc.encLit ⟨l⟩).length st (st.intern (.lit l))
      (evaluateHOLFiniteState t (eLitTail (rRestE 17 (vv lEn) lFle))) := by
  have W : ∀ y, y ∈ bvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  let dd := st.derOfView (.lit l)
  have hdd : dd = Der.litDataW (ConLeche.Literal.hash l) := Der.derOfLit_eq ra st l
  unfold eLitTail
  obtain ⟨w1, hw1⟩ := W lDv (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lDv _ (dWN dd).1 w1
    (by rw [hdd]; exact Der.litDataE.eval t _ lhv) hw1)]
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
  have hint := estore_lit st l
  simp only at hint
  exact eRestE_spec t t3 L FLn FLl FLs FLe KB _ 17 (vv lEn) st Enc.encLit Enc.encLit_inj (mkN ETag.lit 0)
    (mkN ETag.lit 1) (2 ^ 26) (fun i hi => by rw [hb0]; exact idxW_mkN ETag.lit 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.lit 1 (by decide) (by decide) i hi) hS.cap
    st.pers.lits st.scr.lits false ⟨l⟩ dd _
    (fun P' S' => { st with pers := { st.pers with lits := P' }, scr := { st.scr with lits := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_lits h1 P' S' h2 h3 h4 h5 h6)
    hS (by decide) (by decide) rfl hwl hR3 hR3.e.p8 hR3.e.s8 hK (fun _ _ => rfl) rfl rfl rfl rfl
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

/-- `lit (natVal n)`: the caller has put the key `0 :: limbs n` at `ekb`, its length in `en`, the limb
count in `nn` and the limbs' address `ekb + 8` in `na`. -/
def eLitNatWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq natHashP (.seq (.assign .local lHv (vv lNh)) (eLitTail rest))

/-- `lit (strVal s)`: the key `1 :: strW s` at `ekb`, its length in `en`, the byte count in `hn` and the
bytes' address `ekb + 8` in `ha`. -/
def eLitStrWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq strHash (.seq (.assign .local lHv (vv lHh)) (eLitTail rest))

def litNatScratch : List MlS := lNh :: lNi :: lHv :: bvarScratch
def litStrScratch : List MlS := lHh :: lHk :: lHv :: bvarScratch

section
variable {σ : Type}

theorem eInternLitNat_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (n : Nat)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encLit ⟨.natVal n⟩).length 17)
    (hK : Words t KB (Enc.encLit ⟨.natVal n⟩)) (hwl : (Enc.encLit ⟨.natVal n⟩).length < 2 ^ 60)
    (hb0 : L.base 17 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 17 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encLit ⟨.natVal n⟩).length))))
    (lna : t.locals.lookup lNa = some (.val (.word (KB + 8))))
    (lnn : t.locals.lookup lNn = some (.val (.word (BitVec.ofNat 64 (Enc.limbs n).length))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ litNatScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes t L FLn FLl FLs FLe KB (Enc.encLit ⟨.natVal n⟩).length st (st.intern (.lit (.natVal n)))
      (evaluateHOLFiniteState t (eLitNatWith (rRestE 17 (vv lEn) lFle))) := by
  have W : ∀ y, y ∈ litNatScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  have hlw : (natWords n).map UInt64.toBitVec = Enc.limbs n := natWords_limbs n
  have hln : (natWords n).length = (Enc.limbs n).length := by rw [← hlw, List.length_map]
  have hkl : (Enc.encLit ⟨.natVal n⟩).length = (Enc.limbs n).length + 1 := by simp [Enc.encLit]
  have hK' : Words t KB (0 :: (natWords n).map UInt64.toBitVec) := by rw [hlw]; exact hK
  unfold eLitNatWith
  have H := natHashP_spec t (KB + 8) (natWords n) (by omega) (words_tail hK') lna (by rw [hln]; exact lnn)
    (W lNh (by decide)) (W lNi (by decide))
  rcases H with hs | ⟨hn, ym, yd, yc, yg, yt, yfr, yh⟩
  · have ⟨res, hres⟩ : ∃ res, (evaluateHOLFiniteState t natHashP).1 = some res := by
      rcases hs with h | ⟨ev, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    rw [seq_abort _ _ _ _ hres]; exact Or.inl hs
  generalize hy : evaluateHOLFiniteState t natHashP = q at hn ym yd yc yg yt yfr yh
  obtain ⟨qr, y⟩ := q
  simp only at hn ym yd yc yg yt yfr yh; subst hn
  rw [seq_normal _ hy]
  obtain ⟨wh, hwh⟩ := W lHv (by decide)
  have hh : (foldW (natWords n)) = ConLeche.Literal.hash (.natVal n) := by
    show _ = ConLeche.natHash n; rw [natHash_eq ra, leanNatHash_foldW]
  rw [seq_normal _ (ConsLoop.assign_local y lHv _ _ wh (eval_vv y lNh _ yh)
    (by rw [yfr _ (by decide) (by decide)]; exact hwh))]
  let y1 := setVarHOLFinite lHv (.val (.word (foldW (natWords n)).toBitVec)) y
  have yb : ∀ z, z ≠ lNh → z ≠ lNi → z ≠ lHv → y1.locals.lookup z = t.locals.lookup z := by
    intro z a b c; lk [y1]; exact yfr z a b
  have nd : ∀ z ∈ bvarScratch, z ≠ lNh ∧ z ≠ lNi ∧ z ≠ lHv := by decide
  have m1 : y1.memory = t.memory := ym
  have hR1 : SRep y1 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [m1], by rw [m1], by rw [m1], by rw [m1]⟩ yd
    (fun _ _ _ _ => ⟨fun _ _ => by rw [m1], fun _ _ => by rw [m1]⟩)
  refine eres_back (eLitTail_spec ra y1 L FLn FLl FLs FLe KB st (.natVal n) hR1 hS
    (fun j hj => by rw [m1]; exact ⟨yd ▸ (hK j hj).1, (hK j hj).2⟩) (by omega) hb0 hb1
    (by rw [yb _ (by decide) (by decide) (by decide)]; exact lkb)
    (by rw [yb _ (by decide) (by decide) (by decide)]; exact len)
    (by rw [← hh]; exact lookup_setVar_same _ _ _)
    (by rw [yb _ (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [yb _ (by decide) (by decide) (by decide)]; exact lfle)
    (fun z hz => by
      obtain ⟨a, b, c⟩ := nd z hz
      obtain ⟨w, hw⟩ := W z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
      exact ⟨w, by rw [yb z a b c]; exact hw⟩)) ym yd yc yg yt

theorem eInternLitStr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (s : String)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encLit ⟨.strVal s⟩).length 17)
    (hK : Words t KB (Enc.encLit ⟨.strVal s⟩)) (hwl : (Enc.encLit ⟨.strVal s⟩).length < 2 ^ 61)
    (hb0 : L.base 17 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 17 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encLit ⟨.strVal s⟩).length))))
    (lha : t.locals.lookup lHa = some (.val (.word (KB + 8))))
    (lhn : t.locals.lookup lHn = some (.val (.word (BitVec.ofNat 64 s.toByteArray.data.toList.length))))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ litStrScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes t L FLn FLl FLs FLe KB (Enc.encLit ⟨.strVal s⟩).length st (st.intern (.lit (.strVal s)))
      (evaluateHOLFiniteState t (eLitStrWith (rRestE 17 (vv lEn) lFle))) := by
  have W : ∀ y, y ∈ litStrScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  let bs := s.toByteArray.data.toList
  have hbl : (Enc.encLit ⟨.strVal s⟩).length = bs.length + 1 := by simp [Enc.encLit, Enc.strW, bs]
  unfold eLitStrWith
  have H := strHash_spec t (KB + 8) bs (by omega) (words_tail (w := 1) hK) lha lhn (W lHh (by decide)) (W lHk (by decide))
  simp only at H
  rcases H with hs | ⟨hn, yp⟩
  · have ⟨res, hres⟩ : ∃ res, (evaluateHOLFiniteState t strHash).1 = some res := by
      rcases hs with h | ⟨ev, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    rw [seq_abort _ _ _ _ hres]; exact Or.inl hs
  generalize hy : evaluateHOLFiniteState t strHash = q at hn yp
  obtain ⟨qr, y⟩ := q
  simp only at hn yp; subst hn
  rw [seq_normal _ hy]
  obtain ⟨ym, yd, yc, yg, yt, yfr, yh⟩ := yp
  obtain ⟨wh, hwh⟩ := W lHv (by decide)
  have hh : leanStringHash bs = ConLeche.Literal.hash (.strVal s) := by
    show _ = hash s; rw [show hash s = String.hash s from rfl, ra.stringHash]
  rw [seq_normal _ (ConsLoop.assign_local y lHv _ _ wh (eval_vv y lHh _ yh)
    (by rw [yfr _ (by decide) (by decide) (by decide) (by decide)]; exact hwh))]
  let y1 := setVarHOLFinite lHv (.val (.word (leanStringHash bs).toBitVec)) y
  have yb : ∀ z, z ≠ lHa → z ≠ lHn → z ≠ lHh → z ≠ lHk → z ≠ lHv → y1.locals.lookup z = t.locals.lookup z := by
    intro z a b c d e; lk [y1]; exact yfr z a b c d
  have nd : ∀ z ∈ bvarScratch, z ≠ lHa ∧ z ≠ lHn ∧ z ≠ lHh ∧ z ≠ lHk ∧ z ≠ lHv := by decide
  have m1 : y1.memory = t.memory := ym
  have hR1 : SRep y1 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [m1], by rw [m1], by rw [m1], by rw [m1]⟩ yd
    (fun _ _ _ _ => ⟨fun _ _ => by rw [m1], fun _ _ => by rw [m1]⟩)
  refine eres_back (eLitTail_spec ra y1 L FLn FLl FLs FLe KB st (.strVal s) hR1 hS
    (fun j hj => by rw [m1]; exact ⟨yd ▸ (hK j hj).1, (hK j hj).2⟩) hwl hb0 hb1
    (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lkb)
    (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact len)
    (by rw [← hh]; exact lookup_setVar_same _ _ _)
    (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [yb _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lfle)
    (fun z hz => by
      obtain ⟨a, b, c, d, e⟩ := nd z hz
      obtain ⟨w, hw⟩ := W z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
      exact ⟨w, by rw [yb z a b c d e]; exact hw⟩)) ym yd yc yg yt

end

def lDe := ofString "de"
def lEe := ofString "ee"

/-- `proj n i e`: the caller has put the key `idxW n :: idxW e :: limbs i` at `ekb`, its length in `en`,
the handles in `ep` and `ee`, and `i`'s low word in `iw`. -/
def eProjWith (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFln))
  (.seq (.assign .local lDh (vv lEp))
  (.seq (storeDerived 0 3)
  (.seq (.assign .local lHs (vv lDo1))
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv lEe))
  (.seq (storeDerived 9 10)
  (.seq (.assign .local lDe (vv lDo1))
  (.seq (.assign .local lDv ExprData.projDataE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.cmp .notEqual
      (.op .or [.shift .lsr (vv lEp) (.const 31), .shift .lsr (vv lEe) (.const 31)]) (.const 0))) rest))))))))))

def projScratch : List MlS := [lDh, lDt, lDg, lDi, lDo1, lDo2, lHs, lDe, lDv, lDv2, lSk, lOn, lPg, lSg, lK, lL, lFl]

section
variable {σ : Type}

theorem eInternProj_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (st : EStore) (n : NIdx) (i : Nat) (e : EIdx)
    (hR : SRep t L FLn FLl FLs FLe st) (hS : SepK L FLn FLl FLs FLe KB (Enc.encProj ⟨n, i, e⟩).length 18)
    (hK : Words t KB (Enc.encProj ⟨n, i, e⟩)) (hwl : (Enc.encProj ⟨n, i, e⟩).length < 2 ^ 61)
    (hb0 : L.base 18 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.proj.toUInt64.toBitVec * 67108864)
    (hb1 : L.base 18 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.proj.toUInt64.toBitVec * 67108864)
    (lkb : t.locals.lookup lKb = some (.val (.word KB)))
    (len : t.locals.lookup lEn = some (.val (.word (BitVec.ofNat 64 (Enc.encProj ⟨n, i, e⟩).length))))
    (lep : t.locals.lookup lEp = some (.val (.word (Enc.idxW n))))
    (lee : t.locals.lookup lEe = some (.val (.word (Enc.idxW e))))
    (liw : t.locals.lookup lIw = some (.val (.word (UInt64.ofNat i).toBitVec)))
    (ldir : t.locals.lookup lDir = some (.val (.word L.DIR)))
    (lfln : t.locals.lookup lFln = some (.val (.word FLn)))
    (lfle : t.locals.lookup lFle = some (.val (.word FLe)))
    (hw : ∀ y, y ∈ projScratch → ∃ w, t.locals.lookup y = some (.val (.word w))) :
    ERes t L FLn FLl FLs FLe KB (Enc.encProj ⟨n, i, e⟩).length st (st.intern (.proj n i e))
      (evaluateHOLFiniteState t (eProjWith (rRestE 18 (vv lEn) lFle))) := by
  have W : ∀ y, y ∈ projScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) := hw
  unfold eProjWith
  -- the name's derived word
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t lFl _ FLn wf (eval_vv t lFln _ lfln) hwf)]
  let t1 := setVarHOLFinite lFl (.val (.word FLn)) t
  obtain ⟨wh, hwh⟩ := W lDh (by decide)
  rw [seq_normal _ (ConsLoop.assign_local t1 lDh _ (Enc.idxW n) wh (eval_vv t1 lEp _ (by lk [t1]; exact lep))
    (by lk [t1]; exact hwh))]
  let t2 := setVarHOLFinite lDh (.val (.word (Enc.idxW n))) t1
  have W2 : ∀ y, y ∈ projScratch → y ≠ lFl → y ≠ lDh → ∃ w, t2.locals.lookup y = some (.val (.word w)) := by
    intro y hy a1 a2; obtain ⟨w, hw⟩ := W y hy; exact ⟨w, by lk [t2, t1]; exact hw⟩
  have hR2 : SRep t2 L FLn FLl FLs FLe st := srep_frame hR ⟨rfl, rfl, rfl, rfl⟩ rfl
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  have D1 := nDerived_spec t2 L FLn st.lss.ls.ns hR2.n n (lookup_setVar_same _ _ _) (by lk [t2, t1]; exact ldir)
    (by lk [t2, t1]) (W2 lDt (by decide) (by decide) (by decide)) (W2 lDg (by decide) (by decide) (by decide)) (W2 lDi (by decide) (by decide) (by decide)) (W2 lDo1 (by decide) (by decide) (by decide)) (W2 lDo2 (by decide) (by decide) (by decide))
  obtain ⟨n1, m1, d1, c1, g1, ta1, ck1, o1, o2, fr1, wd1⟩ := D1
  generalize hs1 : evaluateHOLFiniteState t2 (storeDerived 0 3) = q1 at n1 m1 d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1
  obtain ⟨q1r, u3⟩ := q1
  simp only at n1 m1 d1 c1 g1 ta1 ck1 o1 o2 fr1 wd1; subst n1
  rw [seq_normal _ hs1]
  have back1 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl →
      u3.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7; rw [fr1 y a1 a2 a3 a4 a5]; lk [t2, t1]
  have wv1 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ∈ projScratch →
      ∃ w, u3.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by rw [back1 y a1 a2 a3 a4 a5 a6 a7]; exact hw⟩
  let dn := st.lss.ls.ns.derived n
  obtain ⟨whs, hwhs⟩ := wv1 lHs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u3 lHs _ _ whs (eval_vv u3 lDo1 _ o1) hwhs)]
  let u4 := setVarHOLFinite lHs (.val (.word (dWN dn).1)) u3
  -- the expression's derived word
  obtain ⟨wf2, hwf2⟩ : ∃ w, u4.locals.lookup lFl = some (.val (.word w)) :=
    ⟨FLn, by lk [u4]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t2, t1]⟩
  rw [seq_normal _ (ConsLoop.assign_local u4 lFl _ FLe wf2
    (eval_vv u4 lFle _ (by lk [u4]; rw [back1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lfle)) hwf2)]
  let u5 := setVarHOLFinite lFl (.val (.word FLe)) u4
  obtain ⟨wh2, hwh2⟩ : ∃ w, u5.locals.lookup lDh = some (.val (.word w)) :=
    ⟨Enc.idxW n, by lk [u5, u4]; rw [fr1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [t2]⟩
  rw [seq_normal _ (ConsLoop.assign_local u5 lDh _ (Enc.idxW e) wh2
    (eval_vv u5 lEe _ (by lk [u5, u4]; rw [back1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lee)) hwh2)]
  let u6 := setVarHOLFinite lDh (.val (.word (Enc.idxW e))) u5
  have mem6 : u6.memory = t.memory := by show u3.memory = _; rw [m1]; rfl
  have md6 : u6.memaddrs = t.memaddrs := by show u3.memaddrs = _; rw [d1]; rfl
  have hR6 : SRep u6 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [mem6], by rw [mem6], by rw [mem6], by rw [mem6]⟩ md6
    (fun _ _ _ _ => ⟨fun _ _ => by rw [mem6], fun _ _ => by rw [mem6]⟩)
  have wd6 : ∀ y, y = lDt ∨ y = lDg ∨ y = lDi → ∃ w, u6.locals.lookup y = some (.val (.word w)) := by
    intro y hy
    obtain ⟨w, hw⟩ := wd1 y hy
    rcases hy with rfl | rfl | rfl <;> exact ⟨w, by lk [u6, u5, u4]; exact hw⟩
  have D2 := eDerived_spec u6 L FLe st hR6.e e (lookup_setVar_same _ _ _)
    (by lk [u6, u5, u4]; rw [back1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ldir) (by lk [u6, u5])
    (wd6 lDt (Or.inl rfl)) (wd6 lDg (Or.inr (Or.inl rfl))) (wd6 lDi (Or.inr (Or.inr rfl)))
    ⟨_, by lk [u6, u5, u4]; exact o1⟩ ⟨_, by lk [u6, u5, u4]; exact o2⟩
  obtain ⟨n2, m2, d2, c2, g2, ta2, ck2, o1', o2', fr2, wd2⟩ := D2
  generalize hs2 : evaluateHOLFiniteState u6 (storeDerived 9 10) = q2 at n2 m2 d2 c2 g2 ta2 ck2 o1' o2' fr2 wd2
  obtain ⟨q2r, u7⟩ := q2
  simp only at n2 m2 d2 c2 g2 ta2 ck2 o1' o2' fr2 wd2; subst n2
  rw [seq_normal _ hs2]
  have back2 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHs →
      u7.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8; rw [fr2 y a1 a2 a3 a4 a5]; lk [u6, u5, u4]; exact back1 y a1 a2 a3 a4 a5 a6 a7
  have hs7 : u7.locals.lookup lHs = some (.val (.word (dWN dn).1)) := by
    rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [u6, u5, u4]
  let de := st.derived e
  obtain ⟨wde, hwde⟩ : ∃ w, u7.locals.lookup lDe = some (.val (.word w)) := by
    obtain ⟨w, hw⟩ := W lDe (by decide); exact ⟨w, by rw [back2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw⟩
  rw [seq_normal _ (ConsLoop.assign_local u7 lDe _ _ wde (eval_vv u7 lDo1 _ o1') hwde)]
  let u8 := setVarHOLFinite lDe (.val (.word (dWN de).1)) u7
  let dd := st.derOfView (.proj n i e)
  have hdd : dd = ExprData.projDataW dn (UInt64.ofNat i) de := Der.derOfProj_eq ra st n i e
  have wv8 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHs → y ≠ lDe →
      y ∈ projScratch → ∃ w, u8.locals.lookup y = some (.val (.word w)) := fun y a1 a2 a3 a4 a5 a6 a7 a8 a9 hy => by
    obtain ⟨w, hw⟩ := hw y hy; exact ⟨w, by lk [u8]; rw [back2 y a1 a2 a3 a4 a5 a6 a7 a8]; exact hw⟩
  obtain ⟨wv1', hwv1⟩ := wv8 lDv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u8 lDv _ (dWN dd).1 wv1'
    (by
      rw [hdd]
      exact ExprData.projDataE.eval u8 dn _ de (by show u8.locals.lookup lHs = _; lk [u8]; exact hs7)
        (by lk [u8]; rw [back2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact liw)
        (by show u8.locals.lookup lDe = _; lk [u8]; rfl))
    hwv1)]
  let u9 := setVarHOLFinite lDv (.val (.word (dWN dd).1)) u8
  obtain ⟨wv2, hwv2⟩ := wv8 lDv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u9 lDv2 (.const 0) (dWN dd).2 wv2 (eval_const u9 0) (by lk [u9]; exact hwv2))]
  let u10 := setVarHOLFinite lDv2 (.val (.word (dWN dd).2)) u9
  obtain ⟨wsk, hwsk⟩ := wv8 lSk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u10 lSk _ (if EStore.eViewHasScratchChild (.proj n i e) then 1 else 0) wsk
    (eval_sk2 u10 lEp lEe n e (by lk [u10, u9, u8]; rw [back2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lep)
      (by lk [u10, u9, u8]; rw [back2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lee))
    (by lk [u10, u9]; exact hwsk))]
  let u11 := setVarHOLFinite lSk (.val (.word (if EStore.eViewHasScratchChild (.proj n i e) then 1 else 0))) u10
  have mem11 : u11.memory = t.memory := by show u7.memory = _; rw [m2]; exact mem6
  have md11 : u11.memaddrs = t.memaddrs := by show u7.memaddrs = _; rw [d2]; exact md6
  have hc11 : u11.code = t.code := by show u7.code = _; rw [c2]; show u3.code = _; rw [c1]; rfl
  have hg11 : u11.globals = t.globals := by show u7.globals = _; rw [g2]; show u3.globals = _; rw [g1]; rfl
  have ht11 : u11.topAddr = t.topAddr := by show u7.topAddr = _; rw [ta2]; show u3.topAddr = _; rw [ta1]; rfl
  have hR11 : SRep u11 L FLn FLl FLs FLe st := srep_frame hR ⟨by rw [mem11], by rw [mem11], by rw [mem11], by rw [mem11]⟩
    md11 (fun _ _ _ _ => ⟨fun _ _ => by rw [mem11], fun _ _ => by rw [mem11]⟩)
  have g : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHs → y ≠ lDe →
      y ≠ lDv → y ≠ lDv2 → y ≠ lSk → y ∈ projScratch → ∃ w, u11.locals.lookup y = some (.val (.word w)) := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hy
    obtain ⟨w, hw⟩ := wv8 y a1 a2 a3 a4 a5 a6 a7 a8 a9 hy; exact ⟨w, by lk [u11, u10, u9]; exact hw⟩
  have b11 : ∀ y, y ≠ lDo1 → y ≠ lDo2 → y ≠ lDt → y ≠ lDg → y ≠ lDi → y ≠ lDh → y ≠ lFl → y ≠ lHs → y ≠ lDe →
      y ≠ lDv → y ≠ lDv2 → y ≠ lSk → u11.locals.lookup y = t.locals.lookup y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12; lk [u11, u10, u9, u8]; exact back2 y a1 a2 a3 a4 a5 a6 a7 a8
  have hint := estore_proj st n i e
  simp only at hint
  exact eRestE_spec t u11 L FLn FLl FLs FLe KB _ 18 (vv lEn) st Enc.encProj Enc.encProj_inj (mkN ETag.proj 0)
    (mkN ETag.proj 1) (2 ^ 26) (fun i hi => by rw [hb0]; exact idxW_mkN ETag.proj 0 (by decide) (by decide) i hi)
    (fun i hi => by rw [hb1]; exact idxW_mkN ETag.proj 1 (by decide) (by decide) i hi) hS.cap
    st.pers.projs st.scr.projs (EStore.eViewHasScratchChild (.proj n i e)) ⟨n, i, e⟩ dd _
    (fun P' S' => { st with pers := { st.pers with projs := P' }, scr := { st.scr with projs := S' } })
    hint (fun _ _ => rfl) (fun v v' P' S' h1 h2 h3 h4 h5 h6 => erep_projs h1 P' S' h2 h3 h4 h5 h6)
    hS (by decide) (by decide) rfl hwl hR11 hR11.e.p9 hR11.e.s9 (fun j hj => by rw [md11, mem11]; exact hK j hj)
    (fun c _ => by rw [mem11]) md11 hc11 hg11 ht11
    (by lk [u11, u10, u9]) (by lk [u11, u10]) (by lk [u11])
    (by rw [b11 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lfle)
    (by rw [b11 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ldir)
    (by rw [b11 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact lkb)
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨FLe, by lk [u11, u10, u9, u8]; rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; lk [u6, u5]⟩
      · exact g lOn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact g lPg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact g lSg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact g lK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact g lL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun x hx => eval_vv x lEn _ (by
      rw [hx _ (by decide), b11 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact len))

end

end ConPanqueque.V
