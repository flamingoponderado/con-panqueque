import ConPanqueque.Code.Table

/-! # The concrete memory layout

Pancake's memory starts at `base = 2^32` (`pancake/ffi_checker.c` maps it there). Every
region has its own band:
- below `2^24`: the store descriptors (`DIR`), the free lists, the key buffer, the memo
  descriptors;
- from `T0`: one 16 MiB band per store table `(k, tier)`, 38 in all;
- from `M0`: one 16 MiB band per memo region, 37 in all;
- from `E0`: the environment heap; from `H0`: the value heap.

So each disjointness clause of the layout facts is linear arithmetic over band indices. -/

open Flapjack Flapjack.Pancake.PanLang ConPanqueque.T ConPanqueque.V ConRon.Arena

namespace ConPanqueque.Code

def base : Nat := 2 ^ 32
def TW : Nat := 2 ^ 24
def T0 : Nat := 2 ^ 24
def M0 : Nat := T0 + 38 * TW
def E0 : Nat := M0 + 37 * TW
def ENw : Nat := 2 ^ 24
def H0 : Nat := E0 + 8 * ENw
def HNw : Nat := 2 ^ 28

/-- A table's geometry in the band starting at offset `o`: header, `2^14` slots, `2^16` rows, the
derived words, a `2^20`-word key heap. -/
def geoAt (o : Nat) : VGeo where
  n := 2 ^ 14
  b := 14
  cap := 2 ^ 16
  kcap := 2 ^ 20
  C := BitVec.ofNat 64 (base + o)
  S := BitVec.ofNat 64 (base + o + 16)
  R := BitVec.ofNat 64 (base + o + 16 + 8 * 2 ^ 14)
  D := BitVec.ofNat 64 (base + o + 16 + 8 * 2 ^ 14 + 16 * 2 ^ 16)
  KH := BitVec.ofNat 64 (base + o + 16 + 8 * 2 ^ 14 + 32 * 2 ^ 16)

def mIdx : MemoK → Nat
  | .inst1 => 0 | .instL => 1 | .lift => 2 | .abs1 => 3 | .inst1L => 4 | .instLP => 5
def nIdx : MemoNK → Nat
  | .bvarB => 0 | .fvarB => 1
def cIdx : CacheK → Nat
  | .whnfCore => 0 | .whnfCoreCheap => 1 | .whnf => 2 | .infer => 3 | .inferIO => 4 | .defeq => 5
  | .constTy => 6 | .constVal => 7 | .ruleBody => 8

/-- A memo region's index, `< 37`; the eager mode memos sit 9 above the plain ones. -/
def rIdx : Region → Nat
  | .e k => mIdx k
  | .n k => 6 + nIdx k
  | .c k => 8 + cIdx k
  | .m false k => 17 + cIdx k
  | .m true k => 26 + cIdx k
  | .env => 35
  | .tbl => 36

theorem rIdx_lt : ∀ r : Region, rIdx r < 37
  | .e k => by cases k <;> decide
  | .n k => by cases k <;> decide
  | .c k => by cases k <;> decide
  | .m b k => by cases b <;> cases k <;> decide
  | .env => by decide
  | .tbl => by decide

def cOf : Nat → CacheK
  | 0 => .whnfCore | 1 => .whnfCoreCheap | 2 => .whnf | 3 => .infer | 4 => .inferIO | 5 => .defeq
  | 6 => .constTy | 7 => .constVal | _ => .ruleBody

def rOf (i : Nat) : Region :=
  if i < 6 then .e (match i with | 0 => .inst1 | 1 => .instL | 2 => .lift | 3 => .abs1 | 4 => .inst1L | _ => .instLP)
  else if i < 8 then .n (if i = 6 then .bvarB else .fvarB)
  else if i < 17 then .c (cOf (i - 8))
  else if i < 26 then .m false (cOf (i - 17))
  else if i < 35 then .m true (cOf (i - 26))
  else if i = 35 then .env else .tbl

theorem rOf_rIdx : ∀ r : Region, rOf (rIdx r) = r
  | .e k => by cases k <;> rfl
  | .n k => by cases k <;> rfl
  | .c k => by cases k <;> rfl
  | .m b k => by cases b <;> cases k <;> rfl
  | .env => rfl
  | .tbl => rfl

theorem rIdx_inj {r r' : Region} (h : rIdx r = rIdx r') : r = r' := by
  rw [← rOf_rIdx r, ← rOf_rIdx r', h]

/-- Each kind's tag part of its handle words. -/
def tagW : Nat → BitVec 64
  | 1 => NTag.str.toUInt64.toBitVec * 67108864
  | 2 => NTag.num.toUInt64.toBitVec * 67108864
  | 3 => LTag.zero.toUInt64.toBitVec * 67108864
  | 4 => LTag.succ.toUInt64.toBitVec * 67108864
  | 5 => LTag.max.toUInt64.toBitVec * 67108864
  | 6 => LTag.imax.toUInt64.toBitVec * 67108864
  | 7 => LTag.param.toUInt64.toBitVec * 67108864
  | 8 => LsTag.list.toUInt64.toBitVec * 67108864
  | 9 => ETag.bvar.toUInt64.toBitVec * 67108864
  | 10 => ETag.fvar.toUInt64.toBitVec * 67108864
  | 11 => ETag.sort.toUInt64.toBitVec * 67108864
  | 12 => ETag.const.toUInt64.toBitVec * 67108864
  | 13 => 1073741824
  | 14 => ETag.lam.toUInt64.toBitVec * 67108864
  | 15 => ETag.forallE.toUInt64.toBitVec * 67108864
  | 16 => ETag.letE.toUInt64.toBitVec * 67108864
  | 17 => ETag.lit.toUInt64.toBitVec * 67108864
  | 18 => ETag.proj.toUInt64.toBitVec * 67108864
  | _ => 0

def layout : Layout where
  DIR := BitVec.ofNat 64 base
  geo k tier := geoAt (T0 + (2 * k + tier) * TW)
  base k tier := (UInt32.ofNat tier).toUInt64.toBitVec * 2147483648 + tagW k

/-- The concrete context: the layout above, the rest as given. -/
def ctxOf (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (H : List (BitVec 64))
    (saved : Option ConRon.Arena.ModeMemos) (St : ConRon.Arena.EStore) (fe : ConRon.Arena.IFEnv) (EH : List (BitVec 64))
    (envM tblM : Std.HashMap ConRon.Arena.NIdx (BitVec 64)) (pins : ConRon.Arena.Pins) (PO : Nat) : Ctx where
  L := layout
  FLn := BitVec.ofNat 64 (base + 4096)
  FLl := BitVec.ofNat 64 (base + 4104)
  FLs := BitVec.ofNat 64 (base + 4112)
  FLe := BitVec.ofNat 64 (base + 4120)
  KB := BitVec.ofNat 64 (base + 8192)
  code := code
  mG r := BitVec.ofNat 64 (base + 65536 + 64 * (rIdx r % 37))
  mg r := geoAt (M0 + (rIdx r % 37) * TW)
  HB := BitVec.ofNat 64 (base + H0)
  HN := HNw
  H := H
  EO := BitVec.ofNat 64 576
  saved := saved
  St := St
  fe := fe
  EB := BitVec.ofNat 64 (base + E0)
  EN := ENw
  EH := EH
  envM := envM
  tblM := tblM
  pins := pins
  PO := PO

theorem toNat_addr (x : Nat) (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem addr_add (x y : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) :=
  ConPanqueque.Scan.ofNat_add64 x y

/-- Membership in a band's table, as arithmetic on offsets. -/
theorem inR_geoAt (o a : Nat) (ho : o + TW ≤ 2 ^ 34) (ha : a < 2 ^ 64) :
    ConPanqueque.V.inR (geoAt o) (BitVec.ofNat 64 a) ↔ base + o ≤ a ∧ a < base + o + 16 + 8 * 2 ^ 14 + 32 * 2 ^ 16 + 8 * 2 ^ 20 := by
  unfold ConPanqueque.V.inR geoAt
  simp only
  rw [toNat_addr _ (by unfold base TW at *; omega), toNat_addr _ ha, toNat_addr _ (by unfold base TW at *; omega)]

set_option hygiene false in
/-- A layout clause: unfold the concrete addresses, then linear arithmetic. -/
macro "lay_tac" : tactic => `(tactic| (
    intros
    simp only [ctxOf, layout, inR, inAny, geoAt, descAddr, ecell, base,
      M0, T0, TW, E0, H0, ENw, HNw, addr_add, not_exists, not_and, ne_eq, ← BitVec.toNat_inj] at *
    intros
    try simp (disch := omega) only [toNat_addr] at *
    omega))

theorem sepK_layout (w k : Nat) (hw : w ≤ 4) (hk : k < 19) :
    SepK layout (BitVec.ofNat 64 (base + 4096)) (BitVec.ofNat 64 (base + 4104)) (BitVec.ofNat 64 (base + 4112))
      (BitVec.ofNat 64 (base + 4120)) (BitVec.ofNat 64 (base + 8192)) w k where
  pow := fun tier _ => by simp [layout, geoAt]
  cap := fun tier _ => by simp [layout, geoAt]
  dis := by lay_tac
  kbo := by lay_tac
  oth := by lay_tac
  dsc := by
    intro k' tier m hk' ht hm
    refine ⟨by lay_tac, by lay_tac, by lay_tac⟩
  fls := by
    intro F hF
    rcases hF with rfl | rfl | rfl | rfl <;> refine ⟨by lay_tac, by lay_tac, by lay_tac⟩

/-- **The layout facts hold for the concrete layout**, given the environment's and pins' relations. -/
theorem ctxOK_ctxOf (code H saved St fe EH envM tblM pins PO)
    (henv : EnvRel (ctxOf code H saved St fe EH envM tblM pins PO))
    (hpins : PinsE (ctxOf code H saved St fe EH envM tblM pins PO)) :
    CtxOK (ctxOf code H saved St fe EH envM tblM pins PO) where
  sepApp := sepK_layout _ _ (by decide) (by decide)
  b0App := rfl
  b1App := rfl
  kbMemo := by lay_tac
  kbMdesc := by lay_tac
  memoOut := by lay_tac
  mdescOut := by lay_tac
  flMemo := by
    intro r F hF
    rcases hF with rfl | rfl | rfl | rfl <;> lay_tac
  dirMemo := by lay_tac
  mdescMemo := by lay_tac
  memoDis := by
    intro r r' c hne h1 h2
    have hne' : rIdx r % 37 ≠ rIdx r' % 37 := by
      rw [Nat.mod_eq_of_lt (rIdx_lt r), Nat.mod_eq_of_lt (rIdx_lt r')]; exact fun h => hne (rIdx_inj h)
    simp only [ctxOf, inR, geoAt, base, M0, T0, TW] at h1 h2
    have := rIdx_lt r; have := rIdx_lt r'
    simp (disch := omega) only [toNat_addr] at h1 h2
    omega
  heapOut := by lay_tac
  kbHeap := by lay_tac
  heapMemo := by lay_tac
  flHeap := by
    intro i F hi hF
    rcases hF with rfl | rfl | rfl | rfl <;> lay_tac
  dirHeap := by lay_tac
  mdescHeap := by lay_tac
  heapLay := by lay_tac
  heapHigh := by lay_tac
  sepLam := sepK_layout _ _ (by decide) (by decide)
  b0Lam := rfl
  b1Lam := rfl
  sepFor := sepK_layout _ _ (by decide) (by decide)
  b0For := rfl
  b1For := rfl
  sepLet := sepK_layout _ _ (by decide) (by decide)
  b0Let := rfl
  b1Let := rfl
  sepBVar := sepK_layout _ _ (by decide) (by decide)
  b0BVar := rfl
  b1BVar := rfl
  sepProj := sepK_layout _ _ (by decide) (by decide)
  b0Proj := rfl
  b1Proj := rfl
  sepLZ := sepK_layout _ _ (by decide) (by decide)
  b0LZ := rfl
  b1LZ := rfl
  sepLS := sepK_layout _ _ (by decide) (by decide)
  b0LS := rfl
  b1LS := rfl
  sepLM := sepK_layout _ _ (by decide) (by decide)
  b0LM := rfl
  b1LM := rfl
  sepLI := sepK_layout _ _ (by decide) (by decide)
  b0LI := rfl
  b1LI := rfl
  sepLP := sepK_layout _ _ (by decide) (by decide)
  b0LP := rfl
  b1LP := rfl
  sepLs := sepK_layout _ _ (by decide) (by decide)
  b0Ls := rfl
  b1Ls := rfl
  sepSort := sepK_layout _ _ (by decide) (by decide)
  b0Sort := rfl
  b1Sort := rfl
  sepConst := sepK_layout _ _ (by decide) (by decide)
  b0Const := rfl
  b1Const := rfl
  sepFVar := sepK_layout _ _ (by decide) (by decide)
  b0FVar := rfl
  b1FVar := rfl
  sepLit := sepK_layout _ _ (by decide) (by decide)
  b0Lit := rfl
  b1Lit := rfl
  eoSide := by intro k; cases k <;> (simp only [ctxOf, rIdx, cIdx]; bv_omega)
  eoNe := by simp only [ctxOf]; decide
  envOut := by lay_tac
  kbEnv := by lay_tac
  envMemo := by lay_tac
  flEnv := by
    intro i F hi hF
    rcases hF with rfl | rfl | rfl | rfl <;> lay_tac
  dirEnv := by lay_tac
  mdescEnv := by lay_tac
  heapEnv := by lay_tac
  envRel := henv
  pinsRel := hpins
  heapCap := by lay_tac
  envLay := by lay_tac

/-- **The frontend's layout facts hold for the concrete layout.** -/
theorem frontOK_ctxOf (code H saved St fe EH envM tblM pins PO) :
    ConPanqueque.Front.FrontOK (ctxOf code H saved St fe EH envM tblM pins PO) where
  sepNS := sepK_layout _ _ (by decide) (by decide)
  b0NS := rfl
  b1NS := rfl
  sepNN := sepK_layout _ _ (by decide) (by decide)
  b0NN := rfl
  b1NN := rfl

end ConPanqueque.Code
