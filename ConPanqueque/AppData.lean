import ConPanqueque.DataWord
import ConPanqueque.Hash
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Hash ConPanqueque.DataWord

/-!
# The data word of an application node

`appDataExp fd ad` is a Pancake expression computing `(Expr.app f a).data`
from the children's data words: the hash by `mixExp` (native multiply), the
range fields by shifts, `max` as `x + (y - x) * [x < y]`, `||` as `max` of bits.
`eval_appDataExp` proves it under the runtime assumption on `mixHash`.
-/

namespace ConPanqueque.AppData

theorem max_bv (x y : UInt64) :
    (max x y).toBitVec = x.toBitVec + (y.toBitVec - x.toBitVec) * (if x.toBitVec < y.toBitVec then 1 else 0) := by
  rw [UInt64.max_def]
  by_cases h : x.toBitVec < y.toBitVec
  · have hle : x ≤ y := UInt64.le_iff_toBitVec_le.mpr (by bv_omega)
    simp [h, hle]; bv_omega
  · by_cases hle : x ≤ y
    · have : x.toBitVec = y.toBitVec := by have := UInt64.le_iff_toBitVec_le.mp hle; bv_omega
      simp [h, hle, this]
    · simp [h, hle]

theorem or_bit (a b : Bool) :
    (if (a || b) then (1 : BitVec 64) else 0) =
      (if a then 1 else 0) + ((if b then 1 else 0) - (if a then 1 else 0)) *
        (if (if a then (1 : BitVec 64) else 0) < (if b then 1 else 0) then 1 else 0) := by
  cases a <;> cases b <;> decide

/-- `max` in the form the Pancake code computes it. -/
def maxW (x y : BitVec 64) : BitVec 64 := x + (y - x) * (if x < y then 1 else 0)
def hashF (w : BitVec 64) : BitVec 64 := w >>> 32
def bvF (w : BitVec 64) : BitVec 64 := (w <<< 33) >>> 49
def fvF (w : BitVec 64) : BitVec 64 := (w <<< 48) >>> 49
def lpF (w : BitVec 64) : BitVec 64 := (w <<< 63) >>> 63

theorem app_data_bv (ra : RuntimeAssumptions) (f a : ConLeche.Expr) :
    (ConLeche.Expr.app f a).data.toBitVec =
      (((leanMixHash 17 (leanMixHash (ConLeche.hashOfData f.data) (ConLeche.hashOfData a.data))).toBitVec
          <<< 32) >>> 32) * 4294967296#64 +
      maxW (bvF f.data.toBitVec) (bvF a.data.toBitVec) * 65536#64 +
      maxW (fvF f.data.toBitVec) (fvF a.data.toBitVec) * 2#64 +
      maxW (lpF f.data.toBitVec) (lpF a.data.toBitVec) := by
  simp only [ConLeche.Expr.data, packData_bv, hash32_bv, ra.mixHash, max_bv, bvarOfData_bv, fvarOfData_bv]
  rw [or_bit, lpOfData_bv, lpOfData_bv]
  simp [maxW, bvF, fvF, lpF]

def shr (e : ExpHOL 64) (k : BitVec 64) : ExpHOL 64 := .shift .lsr e (.const k)
def shl (e : ExpHOL 64) (k : BitVec 64) : ExpHOL 64 := .shift .lsl e (.const k)
def maxE (x y : ExpHOL 64) : ExpHOL 64 := .op .add [x, .panop .mul [.op .sub [y, x], .cmp .lower x y]]

/-- `(Expr.app f a).data` from the children's data words `fd`, `ad`. -/
def appDataExp (fd ad : ExpHOL 64) : ExpHOL 64 :=
  .op .add [.panop .mul [shr (shl (mixExp (.const 17) (mixExp (shr fd 32) (shr ad 32))) 32) 32, .const 4294967296#64],
    .panop .mul [maxE (shr (shl fd 33) 49) (shr (shl ad 33) 49), .const 65536#64],
    .panop .mul [maxE (shr (shl fd 48) 49) (shr (shl ad 48) 49), .const 2#64],
    maxE (shr (shl fd 63) 63) (shr (shl ad 63) 63)]

theorem eval_appDataExp {σ : Type} (ra : RuntimeAssumptions) (s : PanSemStateFiniteExact 64 σ)
    (fdE adE : ExpHOL 64) (f a : ConLeche.Expr)
    (hf : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) fdE =
      some (.val (.word f.data.toBitVec)))
    (ha : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) adE =
      some (.val (.word a.data.toBitVec))) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (appDataExp fdE adE) =
      some (.val (.word (ConLeche.Expr.app f a).data.toBitVec)) := by
  have hi := eval_mixExp s (shr fdE 32) (shr adE 32) (ConLeche.hashOfData f.data) (ConLeche.hashOfData a.data)
    (by simp [shr, evalHOLExact, hf, wordShiftHOL, hashOfData_bv])
    (by simp [shr, evalHOLExact, ha, wordShiftHOL, hashOfData_bv])
  have ho : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (mixExp (.const 17#64) (mixExp (.shift .lsr fdE (.const 32#64)) (.shift .lsr adE (.const 32#64)))) =
      some (.val (.word (leanMixHash 17 (leanMixHash (ConLeche.hashOfData f.data)
        (ConLeche.hashOfData a.data))).toBitVec)) :=
    eval_mixExp s (.const 17) _ 17 _ (by simp [evalHOLExact]) hi
  rw [app_data_bv ra]
  simp [appDataExp, shr, shl, maxE, evalHOLExact, evalListHOLExact, ho, hf, ha, wordShiftHOL, wordOpHOL,
    wordOp, valueIsWord, valueWord, panOpHOL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, maxW, bvF, fvF, lpF,
    BitVec.add_assoc]

end ConPanqueque.AppData
