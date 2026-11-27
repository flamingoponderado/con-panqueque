import ConPanqueque.T.LitIntern
import ConPanqueque.Start.PinList

/-!
# The basis phase at the startup contexts

The generated phase reads its context only through allocation (the heap's base and capacity), so it is the
same program at any two contexts that agree there (`basisP_congr`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open ConPanqueque.T ConPanqueque.T.Lit

namespace ConPanqueque.Start

section
variable {C C' : Ctx} (h1 : C.HB = C'.HB) (h2 : C.HN = C'.HN)
include h1 h2

theorem allocP_congr' (x : MlS) (e : ExpHOL 64) (r : ProgHOL 64) : allocP C x e r = allocP C' x e r := by
  unfold allocP; rw [h1, h2]

theorem genL_congr : ∀ (d : Nat) (u : ConLeche.Level) (r : ProgHOL 64), genL C d u r = genL C' d u r
  | d, .zero, r => rfl
  | d, .succ u, r => by simp only [genL, genL_congr d u]
  | d, .max u v, r => by simp only [genL, genL_congr d u, genL_congr (d + 1) v]
  | d, .imax u v, r => by simp only [genL, genL_congr d u, genL_congr (d + 1) v]
  | d, .param n, r => by simp only [genL, nameP_congr h1 h2]

theorem fillLs_congr (d : Nat) : ∀ (us : List ConLeche.Level) (i : Nat) (r : ProgHOL 64),
    fillLs C d us i r = fillLs C' d us i r
  | [], _, _ => rfl
  | u :: us, i, r => by simp only [fillLs, genL_congr h1 h2, fillLs_congr d us]

theorem genLs_congr (d : Nat) (us : List ConLeche.Level) (r : ProgHOL 64) : genLs C d us r = genLs C' d us r := by
  unfold genLs; rw [allocP_congr' h1 h2, fillLs_congr h1 h2]

theorem genE_congr : ∀ (d : Nat) (e : ConLeche.Expr) (r : ProgHOL 64), genE C d e r = genE C' d e r
  | d, .bvar _, r => rfl
  | d, .sort u, r => by simp only [genE, genL_congr h1 h2]
  | d, .const n us, r => by simp only [genE, nameP_congr h1 h2, genLs_congr h1 h2]
  | d, .app f a, r => by simp only [genE, genE_congr d f, genE_congr (d + 1) a]
  | d, .lam t b, r => by simp only [genE, genE_congr d t, genE_congr (d + 1) b]
  | d, .forallE t b, r => by simp only [genE, genE_congr d t, genE_congr (d + 1) b]
  | d, .lit _, r => rfl
  | d, .fvar _ _, r => rfl
  | d, .letE _ _ _, r => rfl
  | d, .proj _ _ _, r => rfl

theorem genNames_congr : ∀ (ns : List ConLeche.Name) (r : ProgHOL 64), genNames C ns r = genNames C' ns r
  | [], _ => rfl
  | n :: ns, r => by simp only [genNames, nameP_congr h1 h2, genNames_congr ns]

theorem genLvls_congr (d : Nat) : ∀ (us : List ConLeche.Level) (r : ProgHOL 64), genLvls C d us r = genLvls C' d us r
  | [], _ => rfl
  | u :: us, r => by simp only [genLvls, genL_congr h1 h2, genLvls_congr d us]

theorem genCV_congr (d : Nat) (cv : ConLeche.ConstantVal) (r : ProgHOL 64) : genCV C d cv r = genCV C' d cv r := by
  simp only [genCV, nameP_congr h1 h2, genNames_congr h1 h2, genE_congr h1 h2]

theorem genFire_congr (d : Nat) (f : ConLeche.RecRuleFire) (r : ProgHOL 64) : genFire C d f r = genFire C' d f r := by
  cases f <;> simp only [genFire, genLvls_congr h1 h2]

theorem genRule_congr (d : Nat) (rl : ConLeche.RecRule) (r : ProgHOL 64) : genRule C d rl r = genRule C' d rl r := by
  simp only [genRule, nameP_congr h1 h2, genFire_congr h1 h2, genE_congr h1 h2]

theorem genRules_congr (d : Nat) : ∀ (rs : List ConLeche.RecRule) (r : ProgHOL 64), genRules C d rs r = genRules C' d rs r
  | [], _ => rfl
  | rl :: rs, r => by simp only [genRules, genRule_congr h1 h2, genRules_congr d rs]

theorem genCI_congr (d : Nat) (c : ConLeche.ConstantInfo) (r : ProgHOL 64) : genCI C d c r = genCI C' d c r := by
  cases c <;> simp only [genCI, genCV_congr h1 h2, genE_congr h1 h2, genNames_congr h1 h2, nameP_congr h1 h2,
    genRules_congr h1 h2]

theorem genCIList_congr (d : Nat) : ∀ (cs : List ConLeche.ConstantInfo) (r : ProgHOL 64),
    genCIList C d cs r = genCIList C' d cs r
  | [], _ => rfl
  | c :: cs, r => by simp only [genCIList, genCI_congr h1 h2, genCIList_congr d cs]

theorem basisP_congr : ∀ (ks : List ConLeche.BasisKind) (r : ProgHOL 64), basisP C ks r = basisP C' ks r
  | [], _ => rfl
  | k :: ks, r => by simp only [basisP, genCIList_congr h1 h2, basisP_congr ks]

end

/-- The phase's locals: each family to the depth bound. -/
def basisLocals : List MlS :=
  (['l', 'e', 'k', 's', 'n'].flatMap fun c => (List.range 12).map (gv c))

theorem gv_mem_basisLocals {c : Char} (hc : c ∈ ['l', 'e', 'k', 's', 'n']) {j : Nat} (hj : j < 12) :
    gv c j ∈ basisLocals := by
  simp only [basisLocals, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨c, hc, j, hj, rfl⟩

end ConPanqueque.Start
