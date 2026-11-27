import ConPanqueque.Start.PinPhase

/-! # The forbidden-name pass

The bridge to con-leche's pipeline needs every stream record's name to differ from the prelude's
names and from the names the environment's guards read.  All of them are pinned handles (and
`Bool.rec`), held in environment-heap cells.  `forbidP` walks the declaration registry and halts on
any record whose name word equals one of those cells' words (`forbid_spec`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConRon.Arena

namespace ConPanqueque.Start

open ConPanqueque.Front

variable {σ : Type}

def vFk := ofString "fbk"
def vFc := ofString "fbc"
def vFr := ofString "fbr"
def vFn := ofString "fbn"
def vFw := ofString "fbw"

theorem step_skipI {P : PState σ → Prop} : Step P .skip P := fun t ht => by
  rw [ConPanqueque.ConsProbe.skip_eval]; exact Or.inr ⟨rfl, ht⟩

theorem step_envLoadI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (x : MlS) (e : ExpHOL 64) (j : Nat)
    (w : BitVec 64) (hx : x ∈ D) (he : sev Γ e = some (ecell C j)) (hw : C.EH[j]? = some w) :
    Step (Inv (σ := σ) C s Γ M D) (.assign .local x (.load .one e)) (Inv C s ((x, w) :: Γ) M D) := by
  intro t ht
  obtain ⟨hj, hjw⟩ := List.getElem?_eq_some_iff.mp hw
  obtain ⟨w0, h0⟩ := ht.decl x hx
  have hE := ht.sr.env.1
  have hv : EV t (.load .one e) = some (.val (.word w)) := by
    rw [EV, eval_load_word t _ _ (inv_ev ht he) (hE.dom j (Nat.lt_of_lt_of_le hj hE.len))]
    have := hE.val j hj; unfold ecell at he; rw [← hjw]; unfold ecell at this ⊢; rw [this]
  rw [ConsLoop.assign_local t x _ w w0 hv h0]
  exact Or.inr ⟨rfl, inv_set ht x w⟩

theorem sev_eqW (Γ : Env) (a b : ExpHOL 64) (x y : BitVec 64) (ha : sev Γ a = some x) (hb : sev Γ b = some y) :
    sev Γ (.cmp .equal a b) = some (if x = y then 1 else 0) := by
  simp only [sev, ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- Compare the name word in `vFn` with each cell's word; halt on a match. -/
def chkP : List Nat → ProgHOL 64
  | [] => .skip
  | j :: js => .seq (.assign .local vFw (.load .one (.const (ecb j))))
      (.seq (.ite (.cmp .equal (vv vFn) (vv vFw)) hang .skip) (chkP js))

theorem chk_step {C : Ctx} {s : AState} {D : List MlS} (hEB : ∀ j, ecell C j = ecb j) (hFw : vFw ∈ D)
    (nm : BitVec 64) : ∀ (cells : List Nat) (Γ : Env), Γ.get vFn = some nm →
    (∀ j ∈ cells, ∃ w, C.EH[j]? = some w) →
    Step (Inv (σ := σ) C s Γ [] D) (chkP cells)
      (fun t => (∀ j ∈ cells, C.EH[j]? ≠ some nm) ∧ ∃ Γ', (∀ y, y ≠ vFw → Γ'.get y = Γ.get y) ∧
        Inv C s Γ' [] D t)
  | [], Γ, _, _ => fun t ht => by
      rw [chkP, ConPanqueque.ConsProbe.skip_eval]
      exact Or.inr ⟨rfl, fun j hj => absurd hj (by simp), Γ, fun _ _ => rfl, ht⟩
  | j :: js, Γ, hn, hc => by
    obtain ⟨w, hw⟩ := hc j (List.mem_cons_self ..)
    refine step_seq (step_envLoadI vFw _ j w hFw (by simp [sev, hEB]) hw) ?_
    have hn' : T.Env.get ((vFw, w) :: Γ) vFn = some nm := by
      simp only [T.Env.get_cons, show vFn ≠ vFw by decide, ite_false]; exact hn
    refine step_seq (Q := fun t => nm ≠ w ∧ Inv C s ((vFw, w) :: Γ) [] D t)
      (step_ifI _ _ (sev_eqW _ (vv vFn) (vv vFw) nm w hn' (by simp [vv, sev, T.Env.get_cons]))
        (fun _ => step_hangI) (fun h0 => fun t ht => by
          rw [ConPanqueque.ConsProbe.skip_eval]
          refine Or.inr ⟨rfl, fun e => ?_, ht⟩
          simp [e] at h0)) ?_
    intro t ⟨hne, ht⟩
    rcases chk_step hEB hFw nm js ((vFw, w) :: Γ) hn' (fun j' hj' => hc j' (List.mem_cons_of_mem _ hj')) t ht with
      hs | ⟨hn2, hall, Γ', hag, hinv⟩
    · exact Or.inl hs
    · refine Or.inr ⟨hn2, fun j' hj' => ?_, Γ', fun y hy => by rw [hag y hy]; simp [T.Env.get_cons, hy], hinv⟩
      rcases List.mem_cons.mp hj' with rfl | hj'
      · rw [hw]; exact fun e => hne (Option.some.inj e).symm
      · exact hall j' hj'

def vFp := ofString "fbp"

/-- A record's name word. -/
def recNameW : IDeclaration → BitVec 64
  | .defnDecl cv _ _ => Enc.idxW cv.name
  | .thmDecl cv _ => Enc.idxW cv.name
  | .opaqueDecl cv _ => Enc.idxW cv.name
  | .axiomDecl cv => Enc.idxW cv.name
  | .quotDecl _ cv => Enc.idxW cv.name
  | _ => 0

theorem recEnc_name {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o : Nat} {d : IDeclaration} (h : RecEnc C F H o d) :
    H[o + 1]? = some (recNameW d) := by
  cases d with
  | defnDecl cv v hint => obtain ⟨-, -, ⟨ol, -, h1, -⟩, -⟩ := h; exact h1
  | thmDecl cv v => obtain ⟨-, -, ⟨ol, -, h1, -⟩, -⟩ := h; exact h1
  | opaqueDecl cv v => obtain ⟨-, -, ⟨ol, -, h1, -⟩, -⟩ := h; exact h1
  | axiomDecl cv => obtain ⟨-, -, ⟨ol, -, h1, -⟩, -⟩ := h; exact h1
  | quotDecl k cv => obtain ⟨-, -, ⟨ol, -, h1, -⟩, -⟩ := h; exact h1
  | _ => exact h.elim

def forbidBody (cells : List Nat) : ProgHOL 64 :=
  .seq (.assign .local vFr (.load .one (vv vFp)))
  (.seq (.assign .local vFn (.load .one (.op .add [vv vFr, .const 8])))
  (.seq (chkP cells)
  (.seq (.assign .local vFk (.op .add [vv vFk, .const 1]))
    (.assign .local vFp (.op .add [vv vFp, .const 8])))))

/-- Walk the registry at `kRB`, halting on a record whose name word is one of `cells`' words. -/
def forbidP (cells : List Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local vFc (.load .one (vv kRB)))
  (.seq (.assign .local vFk (.const 0))
  (.seq (.assign .local vFp (.op .add [vv kRB, .const 8]))
  (.seq (.while (.cmp .lower (vv vFk) (vv vFc)) (forbidBody cells)) rest)))

def forbidVars : List MlS := [vFk, vFc, vFr, vFn, vFw, vFp]

theorem heapGet_of_some {H : List (BitVec 64)} {j : Nat} {w : BitVec 64} (h : H[j]? = some w) :
    ∃ hj : j < H.length, H[j] = w := List.getElem?_eq_some_iff.mp h

set_option maxHeartbeats 2000000 in
/-- **The pass**: it halts on a record whose name word is one of `cells`' words; otherwise the rest
runs knowing every record's name differs from them. -/
theorem forbid_spec {β : Type} {C : Ctx} {s : AState} {Γ0 : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hEB : ∀ j, ecell C j = ecb j) (hD : ∀ x ∈ forbidVars, x ∈ D)
    {F rb capD : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (hcap : 8 * (rb + 1 + capD) < 2 ^ 64) (hRB : Γ0.get kRB = some (cellA C rb))
    (cells : List Nat) (hcells : ∀ j ∈ cells, ∃ w, C.EH[j]? = some w)
    (hk : ∀ Γ' : Env, (∀ y, y ∉ forbidVars → Γ'.get y = Γ0.get y) →
      (∀ k (hk : k < decls.size), ∀ j ∈ cells, C.EH[j]? ≠ some (recNameW decls[k])) →
      SpecR (Inv C s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ0 M D) (forbidP cells rest) s m R := by
  obtain ⟨hcnt, hle, hlay, hFl, hrec⟩ := hdr
  let n := decls.size
  have hx := fun x (h : x ∈ forbidVars) => hD x h
  suffices hM : SpecR (Inv C s Γ0 [] D) (forbidP cells rest) s m R from
    fun t ht => hM t ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩
  unfold forbidP
  obtain ⟨hrbl, hrbw⟩ := heapGet_of_some hcnt
  refine specR_heapLoadI vFc (vv kRB) rb hrbl (hx _ (by simp [forbidVars])) (by simpa [sev, vv] using hRB) ?_
  rw [hrbw]
  refine specR_assignI vFk (.const 0) 0 (hx _ (by simp [forbidVars])) rfl ?_
  refine specR_assignI vFp _ (cellA C (rb + 1)) (hx _ (by simp [forbidVars])) (by
    simp (config := {decide := true}) [sev, vv, T.Env.get_cons, hRB]; rw [← cellA_add8]; rfl) ?_
  have hn64 : n < 2 ^ 64 := by have : n ≤ capD := hle; omega
  -- the loop's points
  let P : LoopPt β → Prop := fun p => p.C = C ∧ p.s = s ∧ p.m = m ∧ ∃ k, k ≤ n ∧
    p.Γ.get vFk = some (BitVec.ofNat 64 k) ∧ p.Γ.get vFp = some (cellA C (rb + 1 + k)) ∧
    p.Γ.get vFc = some (BitVec.ofNat 64 n) ∧ (∀ y, y ∉ forbidVars → p.Γ.get y = Γ0.get y) ∧
    (∀ k' (h : k' < n), k' < k → ∀ j ∈ cells, C.EH[j]? ≠ some (recNameW decls[k']))
  refine specR_whileT (D := D) P ⟨C, s, _, m⟩ ⟨rfl, rfl, rfl, 0, Nat.zero_le _,
    by simp (config := {decide := true}) [T.Env.get_cons], by simp (config := {decide := true}) [T.Env.get_cons],
    by simp (config := {decide := true}) [T.Env.get_cons]; rfl,
    fun y hy => by
      simp only [forbidVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [T.Env.get_cons, hy.1, hy.2.1, hy.2.2.2.2.2],
    fun k' _ h => absurd h (by omega)⟩ (fun p hp _ => ?_)
  obtain ⟨hC, hs, hm, k, hkn, gk, gp, gc, gag, gdone⟩ := hp
  rw [hC, hs, hm]
  refine ⟨bw (k < n), sev_lower _ _ _ k n (by simpa [sev, vv] using gk) (by simpa [sev, vv] using gc) (by omega) hn64,
    fun h0 => ?_, fun h1 => ?_⟩
  · have hkn' : k = n := by
      by_cases h : k < n
      · simp [bw, h] at h0
      · omega
    subst hkn'
    exact hk p.Γ gag (fun k' hk' j hj => gdone k' hk' hk' j hj)
  · have hk' : k < n := by
      by_cases h : k < n
      · exact h
      · simp [bw, h] at h1
    obtain ⟨o, ho, hro⟩ := hrec k hk'
    obtain ⟨hol, how⟩ := heapGet_of_some ho
    obtain ⟨hnl, hnw⟩ := heapGet_of_some (recEnc_name hro)
    unfold forbidBody
    refine step_seq (T.step_heapLoadI vFr (vv vFp) (rb + 1 + k) hol (hx _ (by simp [forbidVars]))
      (by simpa [sev, vv] using gp)) ?_
    rw [how]
    refine step_seq (T.step_heapLoadI vFn _ (o + 1) hnl (hx _ (by simp [forbidVars]))
      (by simp [sev, vv, T.Env.get_cons]; rw [← cellA_add8]; rfl)) ?_
    rw [hnw]
    refine step_seq (chk_step hEB (hx _ (by simp [forbidVars])) (recNameW decls[k]) cells _
      (by simp [T.Env.get_cons]) hcells) ?_
    intro t ⟨hall, Γc, hagc, htc⟩
    have gk' : Γc.get vFk = some (BitVec.ofNat 64 k) := by
      rw [hagc _ (by decide)]; simp (config := {decide := true}) [T.Env.get_cons]; exact gk
    have gp' : Γc.get vFp = some (cellA C (rb + 1 + k)) := by
      rw [hagc _ (by decide)]; simp (config := {decide := true}) [T.Env.get_cons]; exact gp
    rcases step_seq (step_assignI vFk (.op .add [vv vFk, .const 1]) (BitVec.ofNat 64 (k + 1))
        (hx _ (by simp [forbidVars])) (by
          simp [sev, vv, gk']; exact ConPanqueque.Code.addr_add k 1))
      (step_assignI vFp (.op .add [vv vFp, .const 8]) (cellA C (rb + 1 + (k + 1)))
        (hx _ (by simp [forbidVars])) (by
          simp (config := {decide := true}) [sev, vv, T.Env.get_cons, gp']
          exact cellA_add8 C (rb + 1 + k))) t htc with hs | ⟨hn2, hq⟩
    · exact Or.inl hs
    · refine Or.inr ⟨hn2, ⟨C, s, _, m⟩, ⟨rfl, rfl, rfl, k + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩, rfl, hq⟩
      · simp (config := {decide := true}) [T.Env.get_cons]
      · simp (config := {decide := true}) [T.Env.get_cons]
      · simp (config := {decide := true}) [T.Env.get_cons]
        rw [hagc _ (by decide)]; simp (config := {decide := true}) [T.Env.get_cons]; exact gc
      · intro y hy
        have hy' := hy
        simp only [forbidVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
        simp only [T.Env.get_cons, ite_eq_right hy'.2.2.2.2.2, ite_eq_right hy'.1]
        rw [hagc y hy'.2.2.2.2.1]
        simp only [T.Env.get_cons, ite_eq_right hy'.2.2.2.1, ite_eq_right hy'.2.2.1]
        exact gag y hy
      · intro k' hk'n hk'k j hj
        by_cases e : k' = k
        · subst e; exact hall j hj
        · exact gdone k' hk'n (by omega) j hj

end ConPanqueque.Start
