import ConPanqueque.T.Big.Cmp
import ConPanqueque.T.Core.ConstVal
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# A literal's limbs into the value heap

The bignum arithmetic works heap block to heap block. `litToHeap(h)` copies the limbs of the literal at `h`
into a fresh block. A heap store forgets the store-row facts a view gave, so the loop views the handle again
for each limb (`step_eViewI`, the view as a `Step`).
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def cH := ofString "ch"
def cLn := ofString "cln"
def cO := ofString "co"
def cQ := ofString "cq"
def cK := ofString "ck"
def cX := ofString "cx"
def cI := ofString "ci"

@[simp] theorem cH_ne_cLn : cH ≠ cLn := by decide
@[simp] theorem cH_ne_cO : cH ≠ cO := by decide
@[simp] theorem cH_ne_cQ : cH ≠ cQ := by decide
@[simp] theorem cH_ne_cK : cH ≠ cK := by decide
@[simp] theorem cH_ne_cX : cH ≠ cX := by decide
@[simp] theorem cH_ne_cI : cH ≠ cI := by decide
@[simp] theorem cLn_ne_cH : cLn ≠ cH := by decide
@[simp] theorem cLn_ne_cO : cLn ≠ cO := by decide
@[simp] theorem cLn_ne_cQ : cLn ≠ cQ := by decide
@[simp] theorem cLn_ne_cK : cLn ≠ cK := by decide
@[simp] theorem cLn_ne_cX : cLn ≠ cX := by decide
@[simp] theorem cLn_ne_cI : cLn ≠ cI := by decide
@[simp] theorem cO_ne_cH : cO ≠ cH := by decide
@[simp] theorem cO_ne_cLn : cO ≠ cLn := by decide
@[simp] theorem cO_ne_cQ : cO ≠ cQ := by decide
@[simp] theorem cO_ne_cK : cO ≠ cK := by decide
@[simp] theorem cO_ne_cX : cO ≠ cX := by decide
@[simp] theorem cO_ne_cI : cO ≠ cI := by decide
@[simp] theorem cQ_ne_cH : cQ ≠ cH := by decide
@[simp] theorem cQ_ne_cLn : cQ ≠ cLn := by decide
@[simp] theorem cQ_ne_cO : cQ ≠ cO := by decide
@[simp] theorem cQ_ne_cK : cQ ≠ cK := by decide
@[simp] theorem cQ_ne_cX : cQ ≠ cX := by decide
@[simp] theorem cQ_ne_cI : cQ ≠ cI := by decide
@[simp] theorem cK_ne_cH : cK ≠ cH := by decide
@[simp] theorem cK_ne_cLn : cK ≠ cLn := by decide
@[simp] theorem cK_ne_cO : cK ≠ cO := by decide
@[simp] theorem cK_ne_cQ : cK ≠ cQ := by decide
@[simp] theorem cK_ne_cX : cK ≠ cX := by decide
@[simp] theorem cK_ne_cI : cK ≠ cI := by decide
@[simp] theorem cX_ne_cH : cX ≠ cH := by decide
@[simp] theorem cX_ne_cLn : cX ≠ cLn := by decide
@[simp] theorem cX_ne_cO : cX ≠ cO := by decide
@[simp] theorem cX_ne_cQ : cX ≠ cQ := by decide
@[simp] theorem cX_ne_cK : cX ≠ cK := by decide
@[simp] theorem cX_ne_cI : cX ≠ cI := by decide
@[simp] theorem cI_ne_cH : cI ≠ cH := by decide
@[simp] theorem cI_ne_cLn : cI ≠ cLn := by decide
@[simp] theorem cI_ne_cO : cI ≠ cO := by decide
@[simp] theorem cI_ne_cQ : cI ≠ cQ := by decide
@[simp] theorem cI_ne_cK : cI ≠ cK := by decide
@[simp] theorem cI_ne_cX : cI ≠ cX := by decide
@[simp] theorem cH_ne_lFl : cH ≠ lFl := by decide
@[simp] theorem lFl_ne_cH : lFl ≠ cH := by decide
@[simp] theorem cH_ne_lDh : cH ≠ lDh := by decide
@[simp] theorem lDh_ne_cH : lDh ≠ cH := by decide
@[simp] theorem cH_ne_lDt : cH ≠ lDt := by decide
@[simp] theorem lDt_ne_cH : lDt ≠ cH := by decide
@[simp] theorem cH_ne_lDg : cH ≠ lDg := by decide
@[simp] theorem lDg_ne_cH : lDg ≠ cH := by decide
@[simp] theorem cH_ne_lDi : cH ≠ lDi := by decide
@[simp] theorem lDi_ne_cH : lDi ≠ cH := by decide
@[simp] theorem cH_ne_lRp : cH ≠ lRp := by decide
@[simp] theorem lRp_ne_cH : lRp ≠ cH := by decide
@[simp] theorem cH_ne_lRn : cH ≠ lRn := by decide
@[simp] theorem lRn_ne_cH : lRn ≠ cH := by decide
@[simp] theorem cH_ne_lFle : cH ≠ lFle := by decide
@[simp] theorem lFle_ne_cH : lFle ≠ cH := by decide
@[simp] theorem cH_ne_lDir : cH ≠ lDir := by decide
@[simp] theorem lDir_ne_cH : lDir ≠ cH := by decide
@[simp] theorem cH_ne_lFln : cH ≠ lFln := by decide
@[simp] theorem lFln_ne_cH : lFln ≠ cH := by decide
@[simp] theorem cH_ne_lFll : cH ≠ lFll := by decide
@[simp] theorem lFll_ne_cH : lFll ≠ cH := by decide
@[simp] theorem cH_ne_lFls : cH ≠ lFls := by decide
@[simp] theorem lFls_ne_cH : lFls ≠ cH := by decide
@[simp] theorem cH_ne_lKb : cH ≠ lKb := by decide
@[simp] theorem lKb_ne_cH : lKb ≠ cH := by decide
@[simp] theorem cLn_ne_lFl : cLn ≠ lFl := by decide
@[simp] theorem lFl_ne_cLn : lFl ≠ cLn := by decide
@[simp] theorem cLn_ne_lDh : cLn ≠ lDh := by decide
@[simp] theorem lDh_ne_cLn : lDh ≠ cLn := by decide
@[simp] theorem cLn_ne_lDt : cLn ≠ lDt := by decide
@[simp] theorem lDt_ne_cLn : lDt ≠ cLn := by decide
@[simp] theorem cLn_ne_lDg : cLn ≠ lDg := by decide
@[simp] theorem lDg_ne_cLn : lDg ≠ cLn := by decide
@[simp] theorem cLn_ne_lDi : cLn ≠ lDi := by decide
@[simp] theorem lDi_ne_cLn : lDi ≠ cLn := by decide
@[simp] theorem cLn_ne_lRp : cLn ≠ lRp := by decide
@[simp] theorem lRp_ne_cLn : lRp ≠ cLn := by decide
@[simp] theorem cLn_ne_lRn : cLn ≠ lRn := by decide
@[simp] theorem lRn_ne_cLn : lRn ≠ cLn := by decide
@[simp] theorem cLn_ne_lFle : cLn ≠ lFle := by decide
@[simp] theorem lFle_ne_cLn : lFle ≠ cLn := by decide
@[simp] theorem cLn_ne_lDir : cLn ≠ lDir := by decide
@[simp] theorem lDir_ne_cLn : lDir ≠ cLn := by decide
@[simp] theorem cLn_ne_lFln : cLn ≠ lFln := by decide
@[simp] theorem lFln_ne_cLn : lFln ≠ cLn := by decide
@[simp] theorem cLn_ne_lFll : cLn ≠ lFll := by decide
@[simp] theorem lFll_ne_cLn : lFll ≠ cLn := by decide
@[simp] theorem cLn_ne_lFls : cLn ≠ lFls := by decide
@[simp] theorem lFls_ne_cLn : lFls ≠ cLn := by decide
@[simp] theorem cLn_ne_lKb : cLn ≠ lKb := by decide
@[simp] theorem lKb_ne_cLn : lKb ≠ cLn := by decide
@[simp] theorem cO_ne_lFl : cO ≠ lFl := by decide
@[simp] theorem lFl_ne_cO : lFl ≠ cO := by decide
@[simp] theorem cO_ne_lDh : cO ≠ lDh := by decide
@[simp] theorem lDh_ne_cO : lDh ≠ cO := by decide
@[simp] theorem cO_ne_lDt : cO ≠ lDt := by decide
@[simp] theorem lDt_ne_cO : lDt ≠ cO := by decide
@[simp] theorem cO_ne_lDg : cO ≠ lDg := by decide
@[simp] theorem lDg_ne_cO : lDg ≠ cO := by decide
@[simp] theorem cO_ne_lDi : cO ≠ lDi := by decide
@[simp] theorem lDi_ne_cO : lDi ≠ cO := by decide
@[simp] theorem cO_ne_lRp : cO ≠ lRp := by decide
@[simp] theorem lRp_ne_cO : lRp ≠ cO := by decide
@[simp] theorem cO_ne_lRn : cO ≠ lRn := by decide
@[simp] theorem lRn_ne_cO : lRn ≠ cO := by decide
@[simp] theorem cO_ne_lFle : cO ≠ lFle := by decide
@[simp] theorem lFle_ne_cO : lFle ≠ cO := by decide
@[simp] theorem cO_ne_lDir : cO ≠ lDir := by decide
@[simp] theorem lDir_ne_cO : lDir ≠ cO := by decide
@[simp] theorem cO_ne_lFln : cO ≠ lFln := by decide
@[simp] theorem lFln_ne_cO : lFln ≠ cO := by decide
@[simp] theorem cO_ne_lFll : cO ≠ lFll := by decide
@[simp] theorem lFll_ne_cO : lFll ≠ cO := by decide
@[simp] theorem cO_ne_lFls : cO ≠ lFls := by decide
@[simp] theorem lFls_ne_cO : lFls ≠ cO := by decide
@[simp] theorem cO_ne_lKb : cO ≠ lKb := by decide
@[simp] theorem lKb_ne_cO : lKb ≠ cO := by decide
@[simp] theorem cQ_ne_lFl : cQ ≠ lFl := by decide
@[simp] theorem lFl_ne_cQ : lFl ≠ cQ := by decide
@[simp] theorem cQ_ne_lDh : cQ ≠ lDh := by decide
@[simp] theorem lDh_ne_cQ : lDh ≠ cQ := by decide
@[simp] theorem cQ_ne_lDt : cQ ≠ lDt := by decide
@[simp] theorem lDt_ne_cQ : lDt ≠ cQ := by decide
@[simp] theorem cQ_ne_lDg : cQ ≠ lDg := by decide
@[simp] theorem lDg_ne_cQ : lDg ≠ cQ := by decide
@[simp] theorem cQ_ne_lDi : cQ ≠ lDi := by decide
@[simp] theorem lDi_ne_cQ : lDi ≠ cQ := by decide
@[simp] theorem cQ_ne_lRp : cQ ≠ lRp := by decide
@[simp] theorem lRp_ne_cQ : lRp ≠ cQ := by decide
@[simp] theorem cQ_ne_lRn : cQ ≠ lRn := by decide
@[simp] theorem lRn_ne_cQ : lRn ≠ cQ := by decide
@[simp] theorem cQ_ne_lFle : cQ ≠ lFle := by decide
@[simp] theorem lFle_ne_cQ : lFle ≠ cQ := by decide
@[simp] theorem cQ_ne_lDir : cQ ≠ lDir := by decide
@[simp] theorem lDir_ne_cQ : lDir ≠ cQ := by decide
@[simp] theorem cQ_ne_lFln : cQ ≠ lFln := by decide
@[simp] theorem lFln_ne_cQ : lFln ≠ cQ := by decide
@[simp] theorem cQ_ne_lFll : cQ ≠ lFll := by decide
@[simp] theorem lFll_ne_cQ : lFll ≠ cQ := by decide
@[simp] theorem cQ_ne_lFls : cQ ≠ lFls := by decide
@[simp] theorem lFls_ne_cQ : lFls ≠ cQ := by decide
@[simp] theorem cQ_ne_lKb : cQ ≠ lKb := by decide
@[simp] theorem lKb_ne_cQ : lKb ≠ cQ := by decide
@[simp] theorem cK_ne_lFl : cK ≠ lFl := by decide
@[simp] theorem lFl_ne_cK : lFl ≠ cK := by decide
@[simp] theorem cK_ne_lDh : cK ≠ lDh := by decide
@[simp] theorem lDh_ne_cK : lDh ≠ cK := by decide
@[simp] theorem cK_ne_lDt : cK ≠ lDt := by decide
@[simp] theorem lDt_ne_cK : lDt ≠ cK := by decide
@[simp] theorem cK_ne_lDg : cK ≠ lDg := by decide
@[simp] theorem lDg_ne_cK : lDg ≠ cK := by decide
@[simp] theorem cK_ne_lDi : cK ≠ lDi := by decide
@[simp] theorem lDi_ne_cK : lDi ≠ cK := by decide
@[simp] theorem cK_ne_lRp : cK ≠ lRp := by decide
@[simp] theorem lRp_ne_cK : lRp ≠ cK := by decide
@[simp] theorem cK_ne_lRn : cK ≠ lRn := by decide
@[simp] theorem lRn_ne_cK : lRn ≠ cK := by decide
@[simp] theorem cK_ne_lFle : cK ≠ lFle := by decide
@[simp] theorem lFle_ne_cK : lFle ≠ cK := by decide
@[simp] theorem cK_ne_lDir : cK ≠ lDir := by decide
@[simp] theorem lDir_ne_cK : lDir ≠ cK := by decide
@[simp] theorem cK_ne_lFln : cK ≠ lFln := by decide
@[simp] theorem lFln_ne_cK : lFln ≠ cK := by decide
@[simp] theorem cK_ne_lFll : cK ≠ lFll := by decide
@[simp] theorem lFll_ne_cK : lFll ≠ cK := by decide
@[simp] theorem cK_ne_lFls : cK ≠ lFls := by decide
@[simp] theorem lFls_ne_cK : lFls ≠ cK := by decide
@[simp] theorem cK_ne_lKb : cK ≠ lKb := by decide
@[simp] theorem lKb_ne_cK : lKb ≠ cK := by decide
@[simp] theorem cX_ne_lFl : cX ≠ lFl := by decide
@[simp] theorem lFl_ne_cX : lFl ≠ cX := by decide
@[simp] theorem cX_ne_lDh : cX ≠ lDh := by decide
@[simp] theorem lDh_ne_cX : lDh ≠ cX := by decide
@[simp] theorem cX_ne_lDt : cX ≠ lDt := by decide
@[simp] theorem lDt_ne_cX : lDt ≠ cX := by decide
@[simp] theorem cX_ne_lDg : cX ≠ lDg := by decide
@[simp] theorem lDg_ne_cX : lDg ≠ cX := by decide
@[simp] theorem cX_ne_lDi : cX ≠ lDi := by decide
@[simp] theorem lDi_ne_cX : lDi ≠ cX := by decide
@[simp] theorem cX_ne_lRp : cX ≠ lRp := by decide
@[simp] theorem lRp_ne_cX : lRp ≠ cX := by decide
@[simp] theorem cX_ne_lRn : cX ≠ lRn := by decide
@[simp] theorem lRn_ne_cX : lRn ≠ cX := by decide
@[simp] theorem cX_ne_lFle : cX ≠ lFle := by decide
@[simp] theorem lFle_ne_cX : lFle ≠ cX := by decide
@[simp] theorem cX_ne_lDir : cX ≠ lDir := by decide
@[simp] theorem lDir_ne_cX : lDir ≠ cX := by decide
@[simp] theorem cX_ne_lFln : cX ≠ lFln := by decide
@[simp] theorem lFln_ne_cX : lFln ≠ cX := by decide
@[simp] theorem cX_ne_lFll : cX ≠ lFll := by decide
@[simp] theorem lFll_ne_cX : lFll ≠ cX := by decide
@[simp] theorem cX_ne_lFls : cX ≠ lFls := by decide
@[simp] theorem lFls_ne_cX : lFls ≠ cX := by decide
@[simp] theorem cX_ne_lKb : cX ≠ lKb := by decide
@[simp] theorem lKb_ne_cX : lKb ≠ cX := by decide
@[simp] theorem cI_ne_lFl : cI ≠ lFl := by decide
@[simp] theorem lFl_ne_cI : lFl ≠ cI := by decide
@[simp] theorem cI_ne_lDh : cI ≠ lDh := by decide
@[simp] theorem lDh_ne_cI : lDh ≠ cI := by decide
@[simp] theorem cI_ne_lDt : cI ≠ lDt := by decide
@[simp] theorem lDt_ne_cI : lDt ≠ cI := by decide
@[simp] theorem cI_ne_lDg : cI ≠ lDg := by decide
@[simp] theorem lDg_ne_cI : lDg ≠ cI := by decide
@[simp] theorem cI_ne_lDi : cI ≠ lDi := by decide
@[simp] theorem lDi_ne_cI : lDi ≠ cI := by decide
@[simp] theorem cI_ne_lRp : cI ≠ lRp := by decide
@[simp] theorem lRp_ne_cI : lRp ≠ cI := by decide
@[simp] theorem cI_ne_lRn : cI ≠ lRn := by decide
@[simp] theorem lRn_ne_cI : lRn ≠ cI := by decide
@[simp] theorem cI_ne_lFle : cI ≠ lFle := by decide
@[simp] theorem lFle_ne_cI : lFle ≠ cI := by decide
@[simp] theorem cI_ne_lDir : cI ≠ lDir := by decide
@[simp] theorem lDir_ne_cI : lDir ≠ cI := by decide
@[simp] theorem cI_ne_lFln : cI ≠ lFln := by decide
@[simp] theorem lFln_ne_cI : lFln ≠ cI := by decide
@[simp] theorem cI_ne_lFll : cI ≠ lFll := by decide
@[simp] theorem lFll_ne_cI : lFll ≠ cI := by decide
@[simp] theorem cI_ne_lFls : cI ≠ lFls := by decide
@[simp] theorem lFls_ne_cI : lFls ≠ cI := by decide
@[simp] theorem cI_ne_lKb : cI ≠ lKb := by decide
@[simp] theorem lKb_ne_cI : lKb ≠ cI := by decide

def litLoop : ProgHOL 64 :=
  .while (.cmp .lower (vv cI) (vv cLn))
    (.seq eViewP
    (.seq (.assign .local cX (.load .one (.op .add [vv lRp, vv cK])))
    (.seq (.store (vv cQ) (vv cX))
    (.seq (.assign .local cQ (.op .add [vv cQ, .const 8]))
    (.seq (.assign .local cK (.op .add [vv cK, .const 8]))
    (.assign .local cI (.op .add [vv cI, .const 1])))))))

def litCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv cH)) (.seq eViewP
  (.seq (.assign .local cLn (.op .sub [vv lRn, .const 1]))
  (allocP C cO (.panop .mul [.op .add [vv cLn, .const 1], .const 8])
  (.seq (.store (vv cO) (vv cLn))
  (.seq (.assign .local cQ (.op .add [vv cO, .const 8]))
  (.seq (.assign .local cK (.const 8)) (.seq (.assign .local cI (.const 0))
  (.seq litLoop (.return (vv cO)))))))))))

def litLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, cLn, cO, cQ, cK, cX, cI]
def litBody (C : Ctx) : ProgHOL 64 := prologue litLocals (litCore C)

section
variable {σ : Type}

/-- The expression view as a step: afterwards the row's words are memory facts. -/
theorem step_eViewI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h : EIdx) (v : ENodeView)
    (hv : s.store.view h = some v)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D) :
    Step (Inv (σ := σ) C s Γ M D) eViewP (fun t => ∃ P, Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (encEView v).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ) (wordsAt P (encEView v) ++ M) D t) := by
  intro t ht
  rcases eView_spec t C.L C.FLe s.store ht.sr.rep.e h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v', hv', htg, hr⟩
  · exact Or.inl hs
  rw [hv] at hv'; cases hv'
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, hsh, hdt, hdg, hdi, hfr⟩ := hr
  refine Or.inr ⟨hn, P, sr_of_eq ht.sr hm hd hg hc, fun y w hy => ?_, fun b w hb => ?_, fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hrp
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hrn
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hdt
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; rw [htg]; exact hdg
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hdi
    rename_i e1 e2 e3 e4 e5
    rw [hfr y e1 e2 e3 e4 e5]; exact ht.env y w hy
  · simp only [List.mem_append] at hb
    rcases hb with hb | hb
    · rw [hm, hd]; exact wordsAt_mem hW b w hb
    · rw [hm, hd]; exact ht.mem b w hb
  · by_cases e1 : y = lRp
    · subst e1; exact ⟨P, hrp⟩
    by_cases e2 : y = lRn
    · subst e2; exact ⟨_, hrn⟩
    by_cases e3 : y = lDt
    · subst e3; exact ⟨_, hdt⟩
    by_cases e4 : y = lDg
    · subst e4; exact ⟨_, hdg⟩
    by_cases e5 : y = lDi
    · subst e5; exact ⟨_, hdi⟩
    obtain ⟨w, hw⟩ := ht.decl y hy; exact ⟨w, by rw [hfr y e1 e2 e3 e4 e5]; exact hw⟩

theorem step_ex {α : Type} {P : α → PState σ → Prop} {c : ProgHOL 64} {Q : PState σ → Prop}
    (h : ∀ a, Step (P a) c Q) : Step (fun t => ∃ a, P a t) c Q := by
  intro t ⟨a, ht⟩; exact h a t ht

/-- The loop's environment after `i` limbs. -/
def litG (Γ0 : Env) (C : Ctx) (od i : Nat) : Env :=
  (cI, BitVec.ofNat 64 i) :: (cK, BitVec.ofNat 64 (8 * (i + 1))) :: (cQ, cellA C (od + 1 + i)) :: Γ0

theorem ofNat8_succ (i : Nat) : BitVec.ofNat 64 (8 * (i + 1)) + 8 = BitVec.ofNat 64 (8 * (i + 1 + 1)) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]; congr 1

theorem lit_loop {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ0 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (h : EIdx) (n : Nat)
    (hv : s.store.view h = some (.lit (.natVal n))) (B0 : List (BitVec 64)) (od : Nat)
    (hdst : od + 1 + (limbs n).length ≤ B0.length) (h61 : (limbs n).length < 2 ^ 61)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D ∧ cX ∈ D ∧ cQ ∈ D ∧ cK ∈ D ∧ cI ∈ D)
    (hln : Γ0.get cLn = some (BitVec.ofNat 64 (limbs n).length)) (hdh : Γ0.get lDh = some (Enc.idxW h))
    (hfl : Γ0.get lFl = some C.FLe) (hdir : Γ0.get lDir = some C.L.DIR)
    (hn : Γ0.get lRp = none ∧ Γ0.get lRn = none ∧ Γ0.get lDt = none ∧ Γ0.get lDg = none ∧ Γ0.get lDi = none ∧
      Γ0.get cX = none)
    (hr : SpecR (Inv (ctxH C (fillI B0 (limbs n) (od + 1) (limbs n).length)) s
      (litG Γ0 C od (limbs n).length) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (limbs n) (od + 1) 0)) s (litG Γ0 C od 0) [] D) (.seq litLoop rest) s m R := by
  obtain ⟨d1, d2, d3, d4, d5, dx, dq, dk, di⟩ := hD
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hn
  have hl := fillI_length B0 (limbs n) (od + 1)
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest (limbs n).length
    (fun i => ctxH C (fillI B0 (limbs n) (od + 1) i)) (litG Γ0 C od)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i)
      (BitVec.ofNat 64 (limbs n).length) then 1 else 0, by simp [sev, litG, Env.get, hln], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i (limbs n).length (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < (limbs n).length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 (limbs n).length := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  refine step_seq (step_eViewI (C := ctxH C (fillI B0 (limbs n) (od + 1) i)) h _ hv
    (by simp [litG, hdh]) (by simp [litG, hfl]; rfl) (by simp [litG, hdir]; rfl) ⟨d1, d2, d3, d4, d5⟩) ?_
  refine step_ex fun P => ?_
  have hev : encEView (.lit (.natVal n)) = 0 :: limbs n := rfl
  simp only [hev]
  refine step_seq (step_loadI cX _ (P + BitVec.ofNat 64 (8 * (i + 1))) (limbs n)[i] dx
    (by simp [sev, litG]) (wordsAt_get P (0 :: limbs n) (i + 1) (by simp; omega) [])) ?_
  have hdi : od + 1 + i < (ctxH C (fillI B0 (limbs n) (od + 1) i)).H.length := by
    show od + 1 + i < (fillI B0 (limbs n) (od + 1) i).length; rw [hl]; omega
  refine step_seq (step_heapStoreI (ctxOK_H hok _) (vv cQ) (vv cX) (od + 1 + i) hdi (limbs n)[i]
    (by simp [litG]; rfl) (by simp)) ?_
  refine step_seq (step_assignI cQ _ (cellA C (od + 1 + i + 1)) dq (by simp [sev, litG]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI cK _ (BitVec.ofNat 64 (8 * (i + 1 + 1))) dk
    (by simp [sev, litG]; exact ofNat8_succ i)) ?_
  refine step_mono (step_assignI cI _ (BitVec.ofNat 64 (i + 1)) di (by simp [sev, litG]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => ?_)
  have e : (fillI B0 (limbs n) (od + 1) i).set (od + 1 + i) (limbs n)[i] = fillI B0 (limbs n) (od + 1) (i + 1) := by
    simp [fillI, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  refine inv_envMono (by rw [← e]; exact ht) (fun x v hx => ?_)
  simp only [litG, Env.get_cons] at hx ⊢
  by_cases e1 : x = cI
  · subst e1; simp_all
  by_cases e2 : x = cK
  · subst e2; simp_all
  by_cases e3 : x = cQ
  · subst e3; simp_all [Nat.add_assoc]
  simp only [e1, e2, e3, ite_false] at hx
  have f1 : x ≠ cX := by intro e; subst e; rw [n6] at hx; simp at hx
  have f2 : x ≠ lRp := by intro e; subst e; rw [n1] at hx; simp at hx
  have f3 : x ≠ lRn := by intro e; subst e; rw [n2] at hx; simp at hx
  have f4 : x ≠ lDt := by intro e; subst e; rw [n3] at hx; simp at hx
  have f5 : x ≠ lDg := by intro e; subst e; rw [n4] at hx; simp at hx
  have f6 : x ≠ lDi := by intro e; subst e; rw [n5] at hx; simp at hx
  simp [e1, e2, e3, f1, f2, f3, f4, f5, f6, hx]

end

end ConPanqueque.T.Big
