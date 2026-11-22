import ConPanqueque.Logic.Basic
/-!
# Hashing

Lean's `mixHash` is an opaque runtime function (`lean_uint64_mix_hash`); as in
con-pastel, the final theorem will assume it equals `leanMixHash`
(`RuntimeAssumptions`). In Pancake it is a single expression with native
multiplication: `mixHashBody`, proved to compute `leanMixHash`.
-/

namespace ConPanqueque.Hash
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

/-- `lean_uint64_mix_hash` (con-pastel's `ConPastel.leanMixHash`). -/
def leanMixHash (h k : UInt64) : UInt64 :=
  let m : UInt64 := 0xc6a4a7935bd1e995
  let k := k * m
  let k := k ^^^ (k >>> 47)
  let k := k ^^^ m
  let h := h ^^^ k
  h * m

/-- What the final theorem assumes about the Lean runtime. -/
structure RuntimeAssumptions : Prop where
  mixHash : ∀ h k, mixHash h k = leanMixHash h k

def M : ExpHOL 64 := .const 0xc6a4a7935bd1e995#64
def vh : ExpHOL 64 := .var .local (ofString "h")
def vk : ExpHOL 64 := .var .local (ofString "k")
def km : ExpHOL 64 := .panop .mul [vk, M]

/-- `return (h ^ ((km ^ (km >> 47)) ^ m)) * m` with `km = k * m`. -/
def mixHashBody : ProgHOL 64 :=
  .return (.panop .mul [.op .xor [vh, .op .xor [.op .xor [km, .shift .lsr km (.const 47)], M]], M])

theorem mixHashBody_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h k : UInt64)
    (hh : s.locals.lookup (ofString "h") = some (.val (.word h.toBitVec)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k.toBitVec))) :
    (evaluateHOLFiniteState s mixHashBody).1 = some (.returned (.val (.word (leanMixHash h k).toBitVec))) := by
  unfold mixHashBody
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [evalHOLExact, evalListHOLExact, hh, hk, M, vh, vk, km, wordOpHOL, wordOp, valueIsWord, valueWord,
    panOpHOL, wordShiftHOL, shapeOfHOLExact, leanMixHash]

/-- `mixHash he ke` as one Pancake expression. -/
def mixExp (he ke : ExpHOL 64) : ExpHOL 64 :=
  let km : ExpHOL 64 := .panop .mul [ke, M]
  .panop .mul [.op .xor [he, .op .xor [.op .xor [km, .shift .lsr km (.const 47)], M]], M]

theorem eval_mixExp {σ : Type} (s : PanSemStateFiniteExact 64 σ) (he ke : ExpHOL 64) (a b : UInt64)
    (ha : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) he =
      some (.val (.word a.toBitVec)))
    (hb : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) ke =
      some (.val (.word b.toBitVec))) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (mixExp he ke) =
      some (.val (.word (leanMixHash a b).toBitVec)) := by
  simp [mixExp, evalHOLExact, evalListHOLExact, ha, hb, M, wordOpHOL, wordOp, valueIsWord, valueWord,
    panOpHOL, wordShiftHOL, leanMixHash]

end ConPanqueque.Hash
