import ConPanqueque.V.ProbeOnly
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Two tiers of a generic table

A tier's descriptor holds eight words: `S, R, n-1, C, cap, D, KH + 8·kcap,
base`. `withGeoV g body` loads the one the local `g` points at into the
table locals and runs `body`. `internTwo` is every store's `intern` arm:
with the scratch tier on, the persistent probe (skipped when `csk` is
nonzero: a scratch child), then the scratch tier's intern; with it off, the
persistent tier's intern. `twoTier` is the twin's side.
-/

namespace ConPanqueque.V

def ldwV (g : MlS) (k : Nat) : ExpHOL 64 := .load .one (.op .add [vv g, .const (BitVec.ofNat 64 (8 * k))])

def withGeoV (g : MlS) (body : ProgHOL 64) : ProgHOL 64 :=
  .dec lS .one (ldwV g 0) (.dec lR .one (ldwV g 1) (.dec lM .one (ldwV g 2) (.dec lC0 .one (ldwV g 3)
   (.dec lCap .one (ldwV g 4) (.dec lD .one (ldwV g 5) (.dec lKe .one (ldwV g 6) (.dec lHb .one (ldwV g 7) body)))))))

def descV (g : VGeo) (base : BitVec 64) : List (BitVec 64) :=
  [g.S, g.R, BitVec.ofNat 64 (g.n - 1), g.C, BitVec.ofNat 64 g.cap, g.D, g.KH + BitVec.ofNat 64 (8 * g.kcap), base]

def DescV {σ : Type} (t : PanSemStateFiniteExact 64 σ) (G : BitVec 64) (g : VGeo) (base : BitVec 64) : Prop :=
  ∀ k (hk : k < 8), t.memaddrs (G + BitVec.ofNat 64 (8 * k)) ∧
    t.memory (G + BitVec.ofNat 64 (8 * k)) = .word ((descV g base)[k]'(by simp [descV]; omega))

def geoStateV {σ : Type} (t : PanSemStateFiniteExact 64 σ) (g : VGeo) (base : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  setVarHOLFinite lHb (.val (.word base)) (setVarHOLFinite lKe (.val (.word (g.KH + BitVec.ofNat 64 (8 * g.kcap))))
  (setVarHOLFinite lD (.val (.word g.D)) (setVarHOLFinite lCap (.val (.word (BitVec.ofNat 64 g.cap)))
  (setVarHOLFinite lC0 (.val (.word g.C)) (setVarHOLFinite lM (.val (.word (BitVec.ofNat 64 (g.n - 1))))
  (setVarHOLFinite lR (.val (.word g.R)) (setVarHOLFinite lS (.val (.word g.S)) t)))))))

theorem withGeoV_lift {σ : Type}
    (Q : PanSemStateFiniteExact 64 σ → Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ → Prop)
    (hQ : ∀ s x (v : BitVec 64) r, Q (setVarHOLFinite x (.val (.word v)) s) r →
      Q s (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (x, s.locals.lookup x) }))
    (t : PanSemStateFiniteExact 64 σ) (gn : MlS) (G : BitVec 64) (g : VGeo) (base : BitVec 64) (body : ProgHOL 64)
    (hg : t.locals.lookup gn = some (.val (.word G)))
    (hgn : gn ∉ [lS, lR, lM, lC0, lCap, lD, lKe]) (hdesc : DescV t G g base)
    (hb : Q (geoStateV t g base) (evaluateHOLFiniteState (geoStateV t g base) body)) :
    Q t (evaluateHOLFiniteState t (withGeoV gn body)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hgn
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hgn
  have ev : ∀ (s : PanSemStateFiniteExact 64 σ) (k : Nat) (hk : k < 8), s.locals.lookup gn = some (.val (.word G)) →
      s.memory = t.memory → s.memaddrs = t.memaddrs →
      @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (ldwV gn k) =
        some (.val (.word ((descV g base)[k]'(by simp [descV]; omega)))) := by
    intro s k hk h1 h2 h3
    rw [ldwV, eval_load_word s _ _ (eval_add2 s _ _ _ _ (eval_vv s gn _ h1) (eval_const s _))
      (by rw [h3]; exact (hdesc k hk).1), h2, (hdesc k hk).2]
  unfold withGeoV
  rw [dec_word_eq t lS _ g.S _ (by rw [ev t 0 (by decide) hg rfl rfl]; rfl)]; apply hQ
  let t1 := setVarHOLFinite lS (.val (.word g.S)) t
  rw [dec_word_eq t1 lR _ g.R _ (by rw [ev t1 1 (by decide) (by lk [t1]; exact hg) rfl rfl]; rfl)]; apply hQ
  let t2 := setVarHOLFinite lR (.val (.word g.R)) t1
  rw [dec_word_eq t2 lM _ (BitVec.ofNat 64 (g.n - 1)) _ (by rw [ev t2 2 (by decide) (by lk [t2, t1]; exact hg) rfl rfl]; rfl)]
  apply hQ
  let t3 := setVarHOLFinite lM (.val (.word (BitVec.ofNat 64 (g.n - 1)))) t2
  rw [dec_word_eq t3 lC0 _ g.C _ (by rw [ev t3 3 (by decide) (by lk [t3, t2, t1]; exact hg) rfl rfl]; rfl)]; apply hQ
  let t4 := setVarHOLFinite lC0 (.val (.word g.C)) t3
  rw [dec_word_eq t4 lCap _ (BitVec.ofNat 64 g.cap) _
    (by rw [ev t4 4 (by decide) (by lk [t4, t3, t2, t1]; exact hg) rfl rfl]; rfl)]; apply hQ
  let t5 := setVarHOLFinite lCap (.val (.word (BitVec.ofNat 64 g.cap))) t4
  rw [dec_word_eq t5 lD _ g.D _ (by rw [ev t5 5 (by decide) (by lk [t5, t4, t3, t2, t1]; exact hg) rfl rfl]; rfl)]
  apply hQ
  let t6 := setVarHOLFinite lD (.val (.word g.D)) t5
  rw [dec_word_eq t6 lKe _ (g.KH + BitVec.ofNat 64 (8 * g.kcap)) _
    (by rw [ev t6 6 (by decide) (by lk [t6, t5, t4, t3, t2, t1]; exact hg) rfl rfl]; rfl)]; apply hQ
  let t7 := setVarHOLFinite lKe (.val (.word (g.KH + BitVec.ofNat 64 (8 * g.kcap)))) t6
  rw [dec_word_eq t7 lHb _ base _ (by rw [ev t7 7 (by decide) (by lk [t7, t6, t5, t4, t3, t2, t1]; exact hg) rfl rfl]; rfl)]
  apply hQ
  exact hb

def lPg := ofString "pgeo"
def lSg := ofString "sgeo"
def lOn := ofString "son"
def lSk := ofString "csk"

def internTwo : ProgHOL 64 :=
  .ite (vv lOn)
    (.seq (.ite (vv lSk) .skip (withGeoV lPg probeV)) (withGeoV lSg internV))
    (withGeoV lPg internV)

/-- The twin's two-tier intern at one constructor's tables. -/
def twoTier {α ι δ : Type} [BEq α] [Hashable α] (P Sc : Tbl α ι δ) (on sk : Bool) (x : α) (d : δ)
    (mkP mkS : Nat → ι) : Tbl α ι δ × Tbl α ι δ × ι :=
  match (if on && sk then none else P.find? x) with
  | some h => (P, Sc, h)
  | none =>
    if on then (P, (tierInt Sc x d mkS).1, (tierInt Sc x d mkS).2)
    else ((tierInt P x d mkP).1, Sc, (tierInt P x d mkP).2)

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

/-- One tier's table represented, with the twin's table and handles `mkI`. -/
structure TierRepV (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64) (g : VGeo)
    (tb : Tbl α ι δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat) (mkI : Nat → ι) : Prop where
  vt : VT t enc rows ders slots g hu
  inv : Inv (α := α) (homeV enc g.b) rows slots g.n
  rel : TblRel tb rows mkI
  der : tb.der.toList.map dW = ders

omit [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] in
theorem vt_frame {t t' : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {rows : List α}
    {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {g : VGeo} {hu : Nat} (h : VT t enc rows ders slots g hu)
    (hm : ∀ c, inR g c → t'.memory c = t.memory c) (hd : t'.memaddrs = t.memaddrs) :
    VT t' enc rows ders slots g hu := by
  have lK := h.layK; have lD := h.layD; have lR := h.layR; have lS := h.layS; have lC := h.layC; have hule := h.hu_le
  have hle := h.le
  refine ⟨fun j hj => ?_, fun i hi => ?_, h.short, ⟨by rw [hd]; exact h.cnt.1, by rw [hm _ ⟨Nat.le_refl _, by omega⟩]; exact h.cnt.2⟩,
    ⟨by rw [hd]; exact h.top.1, by rw [hm _ ⟨by rw [tn8 _ (by omega)]; omega, by rw [tn8 _ (by omega)]; omega⟩]; exact h.top.2⟩,
    h.hu_le, h.dlen, fun i hi => ?_, h.le, fun i hi => by rw [hd]; exact h.room i hi,
    fun k hk => by rw [hd]; exact h.hroom k hk, lC, lS, lR, lD, lK⟩
  · obtain ⟨v, a1, a2, a3, a4⟩ := h.slot j hj
    have e := tn g.S (8 * j) (by omega)
    exact ⟨v, a1, a2, by rw [hd]; exact a3, by rw [hm _ ⟨by omega, by omega⟩]; exact a4⟩
  · obtain ⟨P, a1, a2, a3, a4, a5, a6, a7⟩ := h.row i hi
    have e := tn g.R (16 * i) (by omega)
    have e8 : (g.R + BitVec.ofNat 64 (16 * i) + 8).toNat = g.R.toNat + 16 * i + 8 := by rw [tn8 _ (by omega), e]
    refine ⟨P, by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hm _ ⟨by omega, by omega⟩]; exact a3,
      by rw [hm _ ⟨by omega, by omega⟩]; exact a4, fun k hk => ⟨by rw [hd]; exact (a5 k hk).1, ?_⟩, a6, a7⟩
    have ek := tn P (8 * k) (by omega)
    rw [hm _ ⟨by omega, by omega⟩]; exact (a5 k hk).2
  · obtain ⟨a1, a2, a3, a4⟩ := h.der i hi
    have e := tn g.D (16 * i) (by omega)
    have e8 : (g.D + BitVec.ofNat 64 (16 * i) + 8).toNat = g.D.toNat + 16 * i + 8 := by rw [tn8 _ (by omega), e]
    exact ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [hm _ ⟨by omega, by omega⟩]; exact a3,
      by rw [hm _ ⟨by omega, by omega⟩]; exact a4⟩

/-- What `internTwo` guarantees: a stop, or `twoTier`'s handle with both tiers' new tables represented and
memory outside the two regions unchanged. -/
def TRes (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64) (hwd : ι → BitVec 64)
    (mkP mkS : Nat → ι) (P Sc : Tbl α ι δ) (gp gs : VGeo) (on sk : Bool) (x : α) (d : δ)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨
    (r.1 = some (.returned (.val (.word (hwd (twoTier P Sc on sk x d mkP mkS).2.2)))) ∧
      (∃ rows ders slots hu, TierRepV r.2 enc dW gp (twoTier P Sc on sk x d mkP mkS).1 rows ders slots hu mkP) ∧
      (∃ rows ders slots hu, TierRepV r.2 enc dW gs (twoTier P Sc on sk x d mkP mkS).2.1 rows ders slots hu mkS) ∧
      r.2.code = t.code ∧ r.2.globals = t.globals ∧ r.2.memaddrs = t.memaddrs ∧ r.2.topAddr = t.topAddr ∧
      ∀ c, ¬ inR gp c → ¬ inR gs c → r.2.memory c = t.memory c)

end

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

/-- The inputs every run needs, in a state `u`. -/
structure Inputs (u : PanSemStateFiniteExact 64 σ) (K : BitVec 64) (L : Nat) (dd : BitVec 64 × BitVec 64) : Prop where
  k : u.locals.lookup lK = some (.val (.word K))
  l : u.locals.lookup lL = some (.val (.word (BitVec.ofNat 64 L)))
  dv : u.locals.lookup lDv = some (.val (.word dd.1))
  dv2 : u.locals.lookup lDv2 = some (.val (.word dd.2))

theorem tierV_run (u : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hwd : ι → BitVec 64) (mkI : Nat → ι) (base : BitVec 64) (icap : Nat)
    (hmk : ∀ i, i < icap → hwd (mkI i) = base + BitVec.ofNat 64 i) (hinj : ∀ x y, enc x = enc y → x = y)
    (tb : Tbl α ι δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat) (g : VGeo)
    (x : α) (d : δ) (K G : BitVec 64) (gn : MlS)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30) (hci : g.cap ≤ icap)
    (hR : TierRepV u enc dW g tb rows ders slots hu mkI) (hdesc : DescV u G g base)
    (hg : u.locals.lookup gn = some (.val (.word G))) (hgn : gn ∉ [lS, lR, lM, lC0, lCap, lD, lKe])
    (hK : Words u K (enc x)) (hKl : (enc x).length < 2 ^ 61)
    (hKout : ∀ i, i < (enc x).length → ¬ inR g (K + BitVec.ofNat 64 (8 * i)))
    (hin : Inputs u K (enc x).length (dW d)) :
    VRes u enc dW hwd mkI tb g x d (evaluateHOLFiniteState u (withGeoV gn internV)) :=
  withGeoV_lift (fun s r => VRes s enc dW hwd mkI tb g x d r) (fun _ _ _ _ h => vres_locals _ h) u gn G g base
    internV hg hgn hdesc
    (internV_spec _ enc dW hwd mkI base icap hmk hinj tb rows ders slots hu g x d K hn hb hcap hci
      (vt_of_eq hR.vt rfl rfl) hR.inv hR.rel hR.der hK hKl hKout
      (by lk [geoStateV]; exact hin.k) (by lk [geoStateV]; exact hin.l) (by lk [geoStateV]) (by lk [geoStateV])
      (by lk [geoStateV]) (by lk [geoStateV]) (by lk [geoStateV]) (by lk [geoStateV])
      (by lk [geoStateV]; exact hin.dv) (by lk [geoStateV]; exact hin.dv2) (by lk [geoStateV]) (by lk [geoStateV]))

theorem probeV_run (u : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hwd : ι → BitVec 64) (mkI : Nat → ι) (base : BitVec 64) (icap : Nat)
    (hmk : ∀ i, i < icap → hwd (mkI i) = base + BitVec.ofNat 64 i) (hinj : ∀ x y, enc x = enc y → x = y)
    (tb : Tbl α ι δ) (rows : List α) (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat) (g : VGeo)
    (x : α) (K G : BitVec 64) (gn : MlS)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30) (hci : g.cap ≤ icap)
    (hR : TierRepV u enc dW g tb rows ders slots hu mkI) (hdesc : DescV u G g base)
    (hg : u.locals.lookup gn = some (.val (.word G))) (hgn : gn ∉ [lS, lR, lM, lC0, lCap, lD, lKe])
    (hK : Words u K (enc x)) (hKl : (enc x).length < 2 ^ 61) (hin : Inputs u K (enc x).length dv) :
    PResV [] u hwd tb x (evaluateHOLFiniteState u (withGeoV gn probeV)) :=
  withGeoV_lift (fun s r => PResV [] s hwd tb x r)
    (fun _ y _ _ h => presV_dec (presV_mono (B := [y]) (fun _ h => absurd h (List.not_mem_nil)) h)) u gn G g base
    probeV hg hgn hdesc
    (probeV_spec _ enc hwd mkI base icap hmk hinj tb rows ders slots hu g x K hn hb hcap hci
      (vt_of_eq hR.vt rfl rfl) hR.inv hR.rel hK hKl
      (by lk [geoStateV]; exact hin.k) (by lk [geoStateV]; exact hin.l) (by lk [geoStateV]) (by lk [geoStateV])
      (by lk [geoStateV]) (by lk [geoStateV]))

theorem tierRepV_frame {t t' : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64}
    {g : VGeo} {tb : Tbl α ι δ} {rows : List α} {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {hu : Nat}
    {mkI : Nat → ι} (h : TierRepV t enc dW g tb rows ders slots hu mkI)
    (hm : ∀ c, inR g c → t'.memory c = t.memory c) (hd : t'.memaddrs = t.memaddrs) :
    TierRepV t' enc dW g tb rows ders slots hu mkI :=
  ⟨vt_frame h.vt hm hd, h.inv, h.rel, h.der⟩

omit [LawfulBEq α] [DecidableEq α] in
theorem twoTier_off (P Sc : Tbl α ι δ) (sk : Bool) (x : α) (d : δ) (mkP mkS : Nat → ι) :
    twoTier P Sc false sk x d mkP mkS = ((tierInt P x d mkP).1, Sc, (tierInt P x d mkP).2) := by
  simp only [twoTier, Bool.false_and, Bool.false_eq_true, ite_false, tierInt]
  cases P.find? x <;> rfl

omit [LawfulBEq α] [DecidableEq α] in
theorem twoTier_sk (P Sc : Tbl α ι δ) (x : α) (d : δ) (mkP mkS : Nat → ι) :
    twoTier P Sc true true x d mkP mkS = (P, (tierInt Sc x d mkS).1, (tierInt Sc x d mkS).2) := by
  simp [twoTier]

omit [LawfulBEq α] [DecidableEq α] in
theorem twoTier_hit (P Sc : Tbl α ι δ) (x : α) (d : δ) (mkP mkS : Nat → ι) (h : ι) (hf : P.find? x = some h) :
    twoTier P Sc true false x d mkP mkS = (P, Sc, h) := by
  simp [twoTier, hf]

omit [LawfulBEq α] [DecidableEq α] in
theorem twoTier_miss (P Sc : Tbl α ι δ) (x : α) (d : δ) (mkP mkS : Nat → ι) (hf : P.find? x = none) :
    twoTier P Sc true false x d mkP mkS = (P, (tierInt Sc x d mkS).1, (tierInt Sc x d mkS).2) := by
  simp [twoTier, hf]

theorem internTwo_spec (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64)
    (hwd : ι → BitVec 64) (mkP mkS : Nat → ι) (bp bs : BitVec 64) (icap : Nat)
    (hmkP : ∀ i, i < icap → hwd (mkP i) = bp + BitVec.ofNat 64 i)
    (hmkS : ∀ i, i < icap → hwd (mkS i) = bs + BitVec.ofNat 64 i) (hinj : ∀ x y, enc x = enc y → x = y)
    (P Sc : Tbl α ι δ) (gp gs : VGeo)
    (rp : List α) (dp : List (BitVec 64 × BitVec 64)) (sp : List Nat) (hup : Nat)
    (rs : List α) (ds : List (BitVec 64 × BitVec 64)) (ss : List Nat) (hus : Nat)
    (on sk : Bool) (x : α) (d : δ) (K Gp Gs : BitVec 64)
    (hnp : gp.n = 2 ^ gp.b) (hbp : gp.b ≤ 56) (hcp : gp.cap < 2 ^ 30) (hcip : gp.cap ≤ icap)
    (hns : gs.n = 2 ^ gs.b) (hbs : gs.b ≤ 56) (hcs : gs.cap < 2 ^ 30) (hcis : gs.cap ≤ icap)
    (hP : TierRepV t enc dW gp P rp dp sp hup mkP) (hS : TierRepV t enc dW gs Sc rs ds ss hus mkS)
    (hdp : DescV t Gp gp bp) (hds : DescV t Gs gs bs) (hdis : ∀ c, inR gp c → ¬ inR gs c)
    (hK : Words t K (enc x)) (hKl : (enc x).length < 2 ^ 61)
    (hKout : ∀ i, i < (enc x).length → ¬ inR gp (K + BitVec.ofNat 64 (8 * i)) ∧ ¬ inR gs (K + BitVec.ofNat 64 (8 * i)))
    (hin : Inputs t K (enc x).length (dW d))
    (hpg : t.locals.lookup lPg = some (.val (.word Gp))) (hsg : t.locals.lookup lSg = some (.val (.word Gs)))
    (hon : t.locals.lookup lOn = some (.val (.word (if on then 1 else 0))))
    (hsk : t.locals.lookup lSk = some (.val (.word (if sk then 1 else 0)))) :
    TRes t enc dW hwd mkP mkS P Sc gp gs on sk x d (evaluateHOLFiniteState t internTwo) := by
  have hpgn : lPg ∉ [lS, lR, lM, lC0, lCap, lD, lKe] := by decide
  have hsgn : lSg ∉ [lS, lR, lM, lC0, lCap, lD, lKe] := by decide
  unfold internTwo; rw [ite_word t _ _ _ _ (eval_vv t lOn _ hon)]
  cases on
  · -- scratch tier off
    simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    unfold TRes; rw [twoTier_off]
    rcases tierV_run t enc dW hwd mkP bp icap hmkP hinj P rp dp sp hup gp x d K Gp lPg hnp hbp hcp hcip hP hdp hpg hpgn
        hK hKl (fun i hi => (hKout i hi).1) hin with
      h | ⟨hr, rows', ders', slots', hu', hT', hi', hrel', hd', c1, c2, c3, c4, c5⟩
    · exact Or.inl h
    · exact Or.inr ⟨hr, ⟨rows', ders', slots', hu', hT', hi', hrel', hd'⟩,
        ⟨rs, ds, ss, hus, tierRepV_frame hS (fun c hc => c5 c (fun hp => hdis c hp hc)) c3⟩, c1, c2, c3, c4,
        fun c hc _ => c5 c hc⟩
  · simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    -- the scratch tier's intern from a state that agrees with `t`
    have scr : ∀ (sk' : Bool) (u : PanSemStateFiniteExact 64 σ), u.memory = t.memory → u.memaddrs = t.memaddrs →
        u.code = t.code → u.globals = t.globals → u.topAddr = t.topAddr →
        (∀ y, u.locals.lookup y = t.locals.lookup y) →
        twoTier P Sc true sk' x d mkP mkS = (P, (tierInt Sc x d mkS).1, (tierInt Sc x d mkS).2) →
        TRes t enc dW hwd mkP mkS P Sc gp gs true sk' x d
          (evaluateHOLFiniteState u (withGeoV lSg internV)) := by
      intro sk' u m dd c g ta hl hA
      have hSu : TierRepV u enc dW gs Sc rs ds ss hus mkS := tierRepV_frame hS (fun b _ => by rw [m]) dd
      have hPu : TierRepV u enc dW gp P rp dp sp hup mkP := tierRepV_frame hP (fun b _ => by rw [m]) dd
      rcases tierV_run u enc dW hwd mkS bs icap hmkS hinj Sc rs ds ss hus gs x d K Gs lSg hns hbs hcs hcis hSu
          (fun k hk => by rw [m, dd]; exact hds k hk) (by rw [hl]; exact hsg) hsgn
          (fun k hk => by rw [m, dd]; exact hK k hk) hKl (fun i hi => (hKout i hi).2)
          ⟨by rw [hl]; exact hin.k, by rw [hl]; exact hin.l, by rw [hl]; exact hin.dv, by rw [hl]; exact hin.dv2⟩ with
        h | ⟨hr, rows', ders', slots', hu', hT', hi', hrel', hd', c1, c2, c3, c4, c5⟩
      · exact Or.inl h
      · unfold TRes; rw [hA]
        exact Or.inr ⟨hr, ⟨rp, dp, sp, hup, tierRepV_frame hPu (fun b hb => c5 b (hdis b hb)) c3⟩,
          ⟨rows', ders', slots', hu', hT', hi', hrel', hd'⟩, by rw [c1, c], by rw [c2, g], by rw [c3, dd],
          by rw [c4, ta], fun b _ hb => by rw [c5 b hb, m]⟩
    have eite := ite_word t (vv lSk) .skip (withGeoV lPg probeV) _ (eval_vv t lSk _ hsk)
    cases sk
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at eite
      rcases probeV_run t enc dW hwd mkP bp icap hmkP hinj P rp dp sp hup gp x K Gp lPg hnp hbp hcp hcip hP hdp hpg hpgn
          hK hKl hin with hs | ⟨m1, d1, c1, g1, ta1, hit | ⟨hf, hr, hfr⟩⟩
      · exact Or.inl (seq_stop _ _ _ (by rw [eite]; exact hs))
      · obtain ⟨h, hf, hr⟩ := hit
        rw [seq_abort _ _ _ _ (by rw [eite]; exact hr), eite]
        unfold TRes; rw [twoTier_hit P Sc x d mkP mkS h hf]
        exact Or.inr ⟨hr, ⟨rp, dp, sp, hup, tierRepV_frame hP (fun b _ => by rw [m1]) d1⟩,
          ⟨rs, ds, ss, hus, tierRepV_frame hS (fun b _ => by rw [m1]) d1⟩, c1, g1, d1, ta1, fun b _ _ => by rw [m1]⟩
      · generalize hq : evaluateHOLFiniteState t (withGeoV lPg probeV) = q at hr hfr m1 d1 c1 g1 ta1 eite
        obtain ⟨q1, u⟩ := q
        simp only at hr; subst hr
        rw [seq_normal _ eite]
        exact scr false u m1 d1 c1 g1 ta1 (fun y => hfr y (by simp)) (twoTier_miss P Sc x d mkP mkS hf)
    · simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true] at eite
      rw [seq_normal _ (eite.trans (skip_evalV t))]
      exact scr true t rfl rfl rfl rfl rfl (fun _ => rfl) (twoTier_sk P Sc x d mkP mkS)

end

end ConPanqueque.V
