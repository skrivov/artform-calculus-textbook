import ArtformRoles.Calculus.Examples.Rosette
import ArtformRoles.Examples

/-!
# Frames, states, scripts and one capture

`sec:frames-calculus`, `sec:capture` and `sec:firewall` of the paper: the
capture signature, in which a state keeps its legality proof and a guarded move
acts only with its certificate; the capture `N×e5` with its certificate, the
position after it, the readings and the score kept through a gate; the rendering
firewall and the silent-score variant of `prop:chess`; and the incompleteness
of the reference procedure outside the bidirectional fragment.
-/

namespace Artform.Roles.Calculus

open Exp

namespace Book

/-! ## Frames, states, scripts and one capture -/

/-- Sig-Primitive, inverted at the last entry. -/
theorem sigWF_last_prim {S : Sig} {ρ : Role} {A : Exp} (h : SigWF (S ++ [.prim ρ A])) :
    (∃ α, Derivable S true (.ty [] ρ A α)) ∧ A.gradefree := by
  generalize hT : S ++ [.prim ρ A] = T at h
  cases h with
  | nil => simp at hT
  | prim _ dA hgf _ =>
    obtain ⟨rfl, he⟩ := List.append_inj' hT rfl
    simp only [List.cons.injEq, Entry.prim.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨_, dA⟩, hgf⟩
  | family | cert | attest | gate =>
    obtain ⟨-, he⟩ := List.append_inj' hT rfl
    simp at he

namespace Chess

/-- The board `(c_B, h_B) : Form`, from declarations `2` and `3`. -/
abbrev board : Exp := .pair (.const 2 0) (.const 3 0)
/-- `Addr(X)`, at declaration `4`: the addressings of a form. -/
abbrev addr (X : Exp) : Exp := .fam 4 (.cons X .nil)
/-- The addressing `A : Addr(board)`, at declaration `5`. -/
abbrev a : Exp := .const 5 0
/-- `Table(x)`, at declaration `6`. -/
abbrev table (x : Exp) : Exp := .fam 6 (.cons x .nil)
/-- `Legal_A(s)`, at declaration `7`. -/
abbrev legal (s : Exp) : Exp := .fam 7 (.cons s .nil)
/-- `State(A) = Σ(s :_W Table(A)). Legal_A(s)`. -/
abbrev state : Exp := .sigma .witness (table a) (legal (.var 0))
/-- `Script(x, y)`, at declaration `8`: declared scripts, total on legal states. -/
abbrev script (x y : Exp) : Exp := .fam 8 (.cons x (.cons y .nil))
/-- `SameAction(f, g)`, at declaration `13`. -/
abbrev sameAction (f g : Exp) : Exp := .fam 13 (.cons f (.cons g .nil))
/-- `Guarded(x, y)`, at declaration `14`: guarded moves, total on their admitted
input. -/
abbrev guarded (x y : Exp) : Exp := .fam 14 (.cons x (.cons y .nil))
/-- The capture `N×e5 : Guarded(A, A)`, at declaration `15`. -/
abbrev nxe5 : Exp := .const 15 0
/-- `Applicable(f, s)`, at declaration `16`. -/
abbrev applicable (f s : Exp) : Exp := .fam 16 (.cons f (.cons s .nil))
/-- `Table_Bool(x)`, at declaration `17`. -/
abbrev tbool (x : Exp) : Exp := .fam 17 (.cons x .nil)
/-- `Num`, at declaration `25`, and `Graphic`, at declaration `27`: renderings. -/
abbrev num : Exp := .fam 25 .nil
abbrev graphic : Exp := .fam 27 .nil
/-- `Score`, at declaration `29`, and `Move`, the closed witness family of move
records, at declaration `30`. -/
abbrev score : Exp := .fam 29 .nil
abbrev move : Exp := .fam 30 .nil

/-- `f x y …` as a left-nested application. -/
abbrev app2 (f x y : Exp) : Exp := .app (.app f x) y
abbrev app3 (f x y z : Exp) : Exp := .app (.app (.app f x) y) z

/-- `comp : Π^0(f :_S Script(A, A)). Π^0(g :_S Script(A, A)). Script(A, A)`. -/
abbrev tyComp : Exp :=
  .pi .free .script (script a a) (.pi .free .script (script a a) (script a a))
/-- `act_T : Π^0(f :_S Script(A, A)). Π^0(t :_W Table(A)). Table(A)`. -/
abbrev tyActT : Exp := .pi .free .script (script a a) (.pi .free .witness (table a) (table a))
/-- `act_L : Π^0 f. Π^0 t. Π^0(ℓ :_W Legal_A(t)). Legal_A(act_T f t)`. -/
abbrev tyActL : Exp := .pi .free .script (script a a) (.pi .free .witness (table a)
  (.pi .free .witness (legal (.var 0)) (legal (app2 (.const 11 0) (.var 2) (.var 1)))))
/-- `attack : Π^0(s :_W State(A)). Table_Bool(A)`. -/
abbrev tyAttack : Exp := .pi .free .witness state (tbool a)
/-- `check : Π^0(f :_S Guarded(A, A)). Π^0(s :_W State(A)). Π^0(b :_W Table_Bool(A)).
Applicable(f, s)`. -/
abbrev tyCheck : Exp := .pi .free .script (guarded a a) (.pi .free .witness state
  (.pi .free .witness (tbool a) (applicable (.var 2) (.var 1))))
/-- `actG_T : Π^0 f. Π^0 s. Π^0(c :_W Applicable(f, s)). Table(A)`. -/
abbrev tyActGT : Exp := .pi .free .script (guarded a a) (.pi .free .witness state
  (.pi .free .witness (applicable (.var 1) (.var 0)) (table a)))
/-- `actG_L : Π^0 f. Π^0 s. Π^0 c. Legal_A(actG_T f s c)`. -/
abbrev tyActGL : Exp := .pi .free .script (guarded a a) (.pi .free .witness state
  (.pi .free .witness (applicable (.var 1) (.var 0))
    (legal (app3 (.const 20 0) (.var 2) (.var 1) (.var 0)))))
/-- `eval : Π^0(s :_W State(A)). Num`, at the rendering role. -/
abbrev tyEval : Exp := .pi .free .witness state num
/-- `r : Π^0(s :_W State(A)). Graphic`, the diagram, at the rendering role. -/
abbrev tyDraw : Exp := .pi .free .witness state graphic
/-- `mv : Π^0(f :_S Guarded(A, A)). Move`, the record of a move. -/
abbrev tyMv : Exp := .pi .free .script (guarded a a) move

/-- The capture signature. Every family's telescope is ordinary into its role,
every primitive is grade-free and family-headed, the guarded move acts only
with its certificate, the score is written through the gate `note`, and the
move made is attested. The primitives postulate the actions, the attack map and
the check: the signature is schematic, a role-valid typing of the capture and
not the rules of chess. -/
def sig : Sig :=
  artforms ++
  [ .prim .form finCode,                                                     -- 2 c_B
    .prim .form (hist (.const 2 0)),                                         -- 3 h_B
    .family [(.form, form)] .presentation,                                   -- 4 Addr
    .prim .presentation (addr board),                                        -- 5 A
    .family [(.presentation, addr board)] .witness,                          -- 6 Table
    .family [(.witness, table a)] .witness,                                  -- 7 Legal
    .family [(.presentation, addr board), (.presentation, addr board)] .script, -- 8 Script
    .prim .script (script a a),                                              -- 9 id_A
    .prim .script tyComp,                                                    -- 10 comp
    .prim .witness tyActT,                                                   -- 11 act_T
    .prim .witness tyActL,                                                   -- 12 act_L
    .family [(.script, script a a), (.script, script a a)] .witness,         -- 13 SameAction
    .family [(.presentation, addr board), (.presentation, addr board)] .script, -- 14 Guarded
    .prim .script (guarded a a),                                             -- 15 N×e5
    .family [(.script, guarded a a), (.witness, state)] .witness,            -- 16 Applicable
    .family [(.presentation, addr board)] .witness,                          -- 17 Table_Bool
    .prim .witness tyAttack,                                                 -- 18 attack
    .prim .witness tyCheck,                                                  -- 19 check
    .prim .witness tyActGT,                                                  -- 20 actG_T
    .prim .witness tyActGL,                                                  -- 21 actG_L
    .prim .witness (table a),                                                -- 22 t₀
    .prim .witness (legal (.const 22 0)),                                    -- 23 ℓ₀
    .prim .witness (legal (.const 22 0)),                                    -- 24 ℓ₁
    .family [] .rendering,                                                   -- 25 Num
    .prim .rendering tyEval,                                                 -- 26 eval
    .family [] .rendering,                                                   -- 27 Graphic
    .prim .rendering tyDraw,                                                 -- 28 r
    .family [] .form,                                                        -- 29 Score
    .family [] .witness,                                                     -- 30 Move
    .prim .witness tyMv,                                                     -- 31 mv
    .gate [(.form, score)] .witness move .form score,                        -- 32 note
    .attest move (.app (.const 31 0) nxe5),                                  -- 33 the move made
    .prim .form score ]                                                      -- 34 T₀

section Derivations

variable {S : Sig} (hS : SigWF S)

/-- `⊢_F (c, h) : Form` for constants `c : FinCode`, `h : Hist(c)`. -/
def dCode {i j : ℕ} (h0 : S.family? 0 = some ([], .form))
    (h1 : S.family? 1 = some ([(.form, finCode)], .form))
    (hc : S.const? i 0 = some (.form, finCode))
    (hh : S.const? j 0 = some (.form, hist (.const i 0))) {Γ : Ctx} :=
  Deriv.mkPair (B := hist (.var 0)) (Deriv.mkConst hc (dFinCode hS h0 (Γ := Γ)))
    (Deriv.mkConst hh (dHist hS h1 (Deriv.mkConst hc (dFinCode hS h0)))) (Book.dForm hS h0 h1)

/-- `⊢_P Addr(X) type`. -/
def dAddr (h4 : S.family? 4 = some ([(.form, form)], .presentation)) {Γ : Ctx} {X : Exp}
    {φ : Eff} (dX : Deriv S true (.tm Γ .form X form φ)) :=
  Deriv.mkTyFam hS h4 (Deriv.mkSpineCons (Δ := []) dX .mkSpineNil)

/-- A family over one argument of the closed type `T`: `⊢ fam k (x) type`. -/
def dFam1 {k : ℕ} {σ ρ : Role} {T : Exp} (hk : S.family? k = some ([(σ, T)], ρ)) {Γ : Ctx}
    {x : Exp} {φ : Eff} (dx : Deriv S true (.tm Γ σ x T φ)) :=
  Deriv.mkTyFam hS hk (Deriv.mkSpineCons (Δ := []) dx .mkSpineNil)

/-- A family over two arguments whose types are closed: `⊢ fam k (x, y) type`. -/
def dFam2 {k : ℕ} {σ τ ρ : Role} {T U : Exp} (hk : S.family? k = some ([(σ, T), (τ, U)], ρ))
    {Γ : Ctx} {x y : Exp} {φ ψ : Eff} (dx : Deriv S true (.tm Γ σ x T φ))
    (dy : Deriv S true (.tm Γ τ y (U.inst x) ψ)) :=
  Deriv.mkTyFam hS hk (Deriv.mkSpineCons (Δ := [(τ, U)]) dx
    (Deriv.mkSpineCons (Δ := []) dy .mkSpineNil))

/-- `⊢_P A : Addr(board)`. -/
def dA (h0 : S.family? 0 = some ([], .form)) (h1 : S.family? 1 = some ([(.form, finCode)], .form))
    (h2 : S.const? 2 0 = some (.form, finCode))
    (h3 : S.const? 3 0 = some (.form, hist (.const 2 0)))
    (h4 : S.family? 4 = some ([(.form, form)], .presentation))
    (h5 : S.const? 5 0 = some (.presentation, addr board)) {Γ : Ctx} :=
  Deriv.mkConst h5 (dAddr hS h4 (dCode hS h0 h1 h2 h3 (Γ := Γ)))

end Derivations

/-- The facts about `sig` used by its derivations, true of every prefix that
contains the entries involved. -/
structure Decls (S : Sig) : Prop where
  h0 : S.family? 0 = some ([], .form)
  h1 : S.family? 1 = some ([(.form, finCode)], .form)
  h2 : S.const? 2 0 = some (.form, finCode)
  h3 : S.const? 3 0 = some (.form, hist (.const 2 0))
  h4 : S.family? 4 = some ([(.form, form)], .presentation)
  h5 : S.const? 5 0 = some (.presentation, addr board)

section Types

variable {S : Sig} (hS : SigWF S) (h : Decls S)

/-- `⊢_P A : Addr(board)`, in any context. -/
def dA' {Γ : Ctx} := dA hS h.h0 h.h1 h.h2 h.h3 h.h4 h.h5 (Γ := Γ)

/-- `⊢_W Table(A) type`. -/
def dTableA (h6 : S.family? 6 = some ([(.presentation, addr board)], .witness)) {Γ : Ctx} :=
  dFam1 hS h6 (dA' hS h (Γ := Γ))

/-- `⊢_W Legal_A(s) type`, for `s : Table(A)`. -/
def dLegal (h7 : S.family? 7 = some ([(.witness, table a)], .witness)) {Γ : Ctx} {x : Exp}
    {φ : Eff} (dx : Deriv S true (.tm Γ .witness x (table a) φ)) :=
  dFam1 hS h7 dx

/-- `⊢_W State(A) type`. -/
def dState (h6 : S.family? 6 = some ([(.presentation, addr board)], .witness))
    (h7 : S.family? 7 = some ([(.witness, table a)], .witness)) {Γ : Ctx} :=
  Deriv.mkTySigma (dTableA hS h h6 (Γ := Γ))
    (dLegal hS h7 (Deriv.mkVar (i := 0) (A := table a) rfl (dTableA hS h h6)))

/-- `⊢_S Script(A, A) type`. -/
def dScriptAA (h8 : S.family? 8 = some ([(.presentation, addr board),
    (.presentation, addr board)], .script)) {Γ : Ctx} :=
  dFam2 hS h8 (dA' hS h (Γ := Γ)) (dA' hS h)

/-- `⊢_S Guarded(A, A) type`. -/
def dGuardedAA (h14 : S.family? 14 = some ([(.presentation, addr board),
    (.presentation, addr board)], .script)) {Γ : Ctx} :=
  dFam2 hS h14 (dA' hS h (Γ := Γ)) (dA' hS h)

end Types

section Actions

variable {S : Sig} (hS : SigWF S) (h : Decls S)
  (h6 : S.family? 6 = some ([(.presentation, addr board)], .witness))
  (h7 : S.family? 7 = some ([(.witness, table a)], .witness))
  (h8 : S.family? 8 = some ([(.presentation, addr board), (.presentation, addr board)], .script))
  (h11 : S.const? 11 0 = some (.witness, tyActT))
  (h14 : S.family? 14 = some ([(.presentation, addr board), (.presentation, addr board)],
    .script))
  (h16 : S.family? 16 = some ([(.script, guarded a a), (.witness, state)], .witness))
  (h17 : S.family? 17 = some ([(.presentation, addr board)], .witness))
  (h20 : S.const? 20 0 = some (.witness, tyActGT))

/-- `⊢_W Π^0(t :_W Table(A)). Table(A) type`. -/
def dTyTT {Γ : Ctx} :=
  Deriv.mkTyPi (q := .free) (dTableA hS h h6 (Γ := Γ)) (dTableA hS h h6) (by decide)

/-- `⊢_W` the type of `act_T`. -/
def dTyActT {Γ : Ctx} :=
  Deriv.mkTyPi (q := .free) (dScriptAA hS h h8 (Γ := Γ)) (dTyTT hS h h6) (by decide)

/-- `⊢_S` the type of `comp`. -/
def dTyComp {Γ : Ctx} :=
  Deriv.mkTyPi (q := .free) (dScriptAA hS h h8 (Γ := Γ))
    (Deriv.mkTyPi (q := .free) (dScriptAA hS h h8) (dScriptAA hS h h8) (by decide)) (by decide)

/-- The context of `act_L`'s result: `f :_S Script(A, A), t :_W Table(A),
ℓ :_W Legal_A(t)`, innermost first. -/
abbrev ΓL : Ctx := [(.witness, legal (.var 0)), (.witness, table a), (.script, script a a)]

/-- `act_T f t : Table(A)` in the context of `act_L`'s result. -/
def dActTVars :=
  Deriv.mkApp (Deriv.mkApp (Deriv.mkConst h11 (dTyActT hS h h6 h8 (Γ := ΓL)))
      (Deriv.mkVar (Γ := ΓL) (i := 2) (A := script a a) rfl (dScriptAA hS h h8))
      (dTyTT hS h h6))
    (Deriv.mkVar (Γ := ΓL) (i := 1) (A := table a) rfl (dTableA hS h h6)) (dTableA hS h h6)

/-- `⊢_W` the type of `act_L`. -/
def dTyActL :=
  Deriv.mkTyPi (q := .free) (Γ := []) (dScriptAA hS h h8)
    (Deriv.mkTyPi (q := .free) (dTableA hS h h6)
      (Deriv.mkTyPi (q := .free)
        (dLegal hS h7 (Deriv.mkVar (i := 0) (A := table a) (by rfl) (dTableA hS h h6)))
        (dLegal hS h7 (dActTVars hS h h6 h8 h11)) (by decide)) (by decide)) (by decide)

/-- `⊢_W Table_Bool(A) type`. -/
def dTBool {Γ : Ctx} := dFam1 hS h17 (dA' hS h (Γ := Γ))

/-- `⊢_W` the type of `attack`. -/
def dTyAttack {Γ : Ctx} :=
  Deriv.mkTyPi (q := .free) (dState hS h h6 h7 (Γ := Γ)) (dTBool hS h h17) (by decide)

/-- `⊢_W Applicable(f, s) type`, for a guarded move `f` and a state `s`. -/
def dApplicable {Γ : Ctx} {f s : Exp} {φ ψ : Eff}
    (df : Deriv S true (.tm Γ .script f (guarded a a) φ))
    (ds : Deriv S true (.tm Γ .witness s state ψ)) :=
  dFam2 hS h16 df ds

/-- `⊢_W Applicable(x_j, x_i) type`, for a guarded-move variable `x_j` and a
state variable `x_i`. -/
def dApplicableAt {Γ : Ctx} {j i : ℕ} (hf : Γ[j]? = some (.script, guarded a a))
    (hs : Γ[i]? = some (.witness, state)) :=
  dApplicable hS h16 (Deriv.mkVar (i := j) (A := guarded a a) hf (dGuardedAA hS h h14))
    (Deriv.mkVar (i := i) (A := state) hs (dState hS h h6 h7))

/-- `⊢_W` the type of `check`. -/
def dTyCheck {Γ : Ctx} :=
  Deriv.mkTyPi (q := .free) (dGuardedAA hS h h14 (Γ := Γ))
    (Deriv.mkTyPi (q := .free) (dState hS h h6 h7)
      (Deriv.mkTyPi (q := .free) (dTBool hS h h17)
        (dApplicableAt hS h h6 h7 h14 h16 (j := 2) (i := 1) (by rfl) (by rfl))
        (by decide)) (by decide)) (by decide)

/-- `⊢_W` the type of `actG_T`. -/
def dTyActGT {Γ : Ctx} :=
  Deriv.mkTyPi (q := .free) (dGuardedAA hS h h14 (Γ := Γ))
    (Deriv.mkTyPi (q := .free) (dState hS h h6 h7)
      (Deriv.mkTyPi (q := .free)
        (dApplicableAt hS h h6 h7 h14 h16 (j := 1) (i := 0) (by rfl) (by rfl))
        (dTableA hS h h6) (by decide)) (by decide)) (by decide)

/-- The context of `actG_L`'s result: `f :_S Guarded(A, A), s :_W State(A),
c :_W Applicable(f, s)`, innermost first. -/
abbrev ΓG : Ctx :=
  [(.witness, applicable (.var 1) (.var 0)), (.witness, state), (.script, guarded a a)]

/-- `actG_T f s c : Table(A)` in the context of `actG_L`'s result. -/
def dActGTVars :=
  Deriv.mkApp
    (Deriv.mkApp
      (Deriv.mkApp (Deriv.mkConst h20 (dTyActGT hS h h6 h7 h14 h16 (Γ := ΓG)))
        (Deriv.mkVar (Γ := ΓG) (i := 2) (A := guarded a a) rfl (dGuardedAA hS h h14))
        (Deriv.mkTyPi (q := .free) (dState hS h h6 h7)
          (Deriv.mkTyPi (q := .free)
            (dApplicableAt hS h h6 h7 h14 h16 (Γ := (.witness, state) :: ΓG) (j := 3) (i := 0)
              rfl rfl)
            (dTableA hS h h6) (by decide)) (by decide)))
      (Deriv.mkVar (Γ := ΓG) (i := 1) (A := state) rfl (dState hS h h6 h7))
      (Deriv.mkTyPi (q := .free)
        (dApplicableAt hS h h6 h7 h14 h16 (Γ := ΓG) (j := 2) (i := 1) rfl rfl)
        (dTableA hS h h6) (by decide)))
    (Deriv.mkVar (Γ := ΓG) (i := 0) (A := applicable (.var 1) (.var 0)) rfl
      (dApplicableAt hS h h6 h7 h14 h16 (Γ := ΓG) (j := 2) (i := 1) rfl rfl))
    (dTableA hS h h6)

/-- `⊢_W` the type of `actG_L`. -/
def dTyActGL :=
  Deriv.mkTyPi (q := .free) (Γ := []) (dGuardedAA hS h h14)
    (Deriv.mkTyPi (q := .free) (dState hS h h6 h7)
      (Deriv.mkTyPi (q := .free)
        (dApplicableAt hS h h6 h7 h14 h16 (j := 1) (i := 0) (by rfl) (by rfl))
        (dLegal hS h7 (dActGTVars hS h h6 h7 h14 h16 h20)) (by decide)) (by decide))
    (by decide)

end Actions

/-- Prefixes of the capture signature with their declarations. -/
theorem decls (n : ℕ) (hn : 6 ≤ n) : Decls (sig.take n) := by
  have h : ∀ i, i < 6 → (sig.take n)[i]? = sig[i]? := fun i hi =>
    List.getElem?_take_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Sig.family?, Sig.const?, h 0 (by omega), h 1 (by omega), h 2 (by omega),
      h 3 (by omega), h 4 (by omega), h 5 (by omega)] <;> rfl

/-- The capture signature is admitted: every family telescope is ordinary into
its role, every primitive is closed, grade-free and family-headed, `note` meets
Sig-Gate with a grade-free interface, and the move made meets Sig-Attest. -/
theorem sig_wf : SigWF sig := by
  have w2 : SigWF (sig.take 2) := artforms_wf
  have w3 : SigWF (sig.take 3) := .prim w2 ⟨dFinCode w2 rfl⟩ trivial ⟨0, .nil, rfl, rfl⟩
  have w4 : SigWF (sig.take 4) :=
    .prim w3 ⟨dHist w3 rfl (Deriv.mkConst rfl (dFinCode w3 rfl))⟩ ⟨trivial, trivial⟩
      ⟨1, _, rfl, rfl⟩
  have w5 : SigWF (sig.take 5) :=
    .family w4 ⟨Deriv.mkTelCons (Book.dForm w4 rfl rfl) .mkTelNil⟩ (by simp [demand])
  have w6 : SigWF (sig.take 6) :=
    .prim w5 ⟨dAddr w5 rfl (dCode w5 rfl rfl rfl rfl)⟩ (by simp [Exp.gradefree])
      ⟨4, _, rfl, rfl⟩
  have w7 : SigWF (sig.take 7) :=
    .family w6 ⟨Deriv.mkTelCons (dAddr w6 rfl (dCode w6 rfl rfl rfl rfl)) .mkTelNil⟩
      (by simp [demand])
  have w8 : SigWF (sig.take 8) :=
    .family w7 ⟨Deriv.mkTelCons (dTableA w7 (decls 7 (by omega)) rfl) .mkTelNil⟩
      (by simp [demand])
  have w9 : SigWF (sig.take 9) :=
    .family w8 ⟨Deriv.mkTelCons (dAddr w8 rfl (dCode w8 rfl rfl rfl rfl))
      (Deriv.mkTelCons (dAddr w8 rfl (dCode w8 rfl rfl rfl rfl)) .mkTelNil)⟩ (by simp [demand])
  have w10 : SigWF (sig.take 10) :=
    .prim w9 ⟨dScriptAA w9 (decls 9 (by omega)) rfl (Γ := [])⟩ (by simp [Exp.gradefree])
      ⟨8, _, rfl, rfl⟩
  have w11 : SigWF (sig.take 11) :=
    .prim w10 ⟨dTyComp w10 (decls 10 (by omega)) rfl (Γ := [])⟩ (by simp [Exp.gradefree])
      ⟨8, _, rfl, rfl⟩
  have w12 : SigWF (sig.take 12) :=
    .prim w11 ⟨dTyActT w11 (decls 11 (by omega)) rfl rfl (Γ := [])⟩ (by simp [Exp.gradefree])
      ⟨6, _, rfl, rfl⟩
  have w13 : SigWF (sig.take 13) :=
    .prim w12 ⟨dTyActL w12 (decls 12 (by omega)) rfl rfl rfl rfl⟩ (by simp [Exp.gradefree])
      ⟨7, _, rfl, rfl⟩
  have w14 : SigWF (sig.take 14) :=
    .family w13 ⟨Deriv.mkTelCons (dScriptAA w13 (decls 13 (by omega)) rfl)
      (Deriv.mkTelCons (dScriptAA w13 (decls 13 (by omega)) rfl) .mkTelNil)⟩ (by simp [demand])
  have w15 : SigWF (sig.take 15) :=
    .family w14 ⟨Deriv.mkTelCons (dAddr w14 rfl (dCode w14 rfl rfl rfl rfl))
      (Deriv.mkTelCons (dAddr w14 rfl (dCode w14 rfl rfl rfl rfl)) .mkTelNil)⟩ (by simp [demand])
  have w16 : SigWF (sig.take 16) :=
    .prim w15 ⟨dGuardedAA w15 (decls 15 (by omega)) rfl (Γ := [])⟩ (by simp [Exp.gradefree])
      ⟨14, _, rfl, rfl⟩
  have w17 : SigWF (sig.take 17) :=
    .family w16 ⟨Deriv.mkTelCons (dGuardedAA w16 (decls 16 (by omega)) rfl)
      (Deriv.mkTelCons (dState w16 (decls 16 (by omega)) rfl rfl) .mkTelNil)⟩ (by simp [demand])
  have w18 : SigWF (sig.take 18) :=
    .family w17 ⟨Deriv.mkTelCons (dAddr w17 rfl (dCode w17 rfl rfl rfl rfl)) .mkTelNil⟩
      (by simp [demand])
  have w19 : SigWF (sig.take 19) :=
    .prim w18 ⟨dTyAttack w18 (decls 18 (by omega)) rfl rfl rfl (Γ := [])⟩
      (by simp [Exp.gradefree]) ⟨17, _, rfl, rfl⟩
  have w20 : SigWF (sig.take 20) :=
    .prim w19 ⟨dTyCheck w19 (decls 19 (by omega)) rfl rfl rfl rfl rfl (Γ := [])⟩
      (by simp [Exp.gradefree]) ⟨16, _, rfl, rfl⟩
  have w21 : SigWF (sig.take 21) :=
    .prim w20 ⟨dTyActGT w20 (decls 20 (by omega)) rfl rfl rfl rfl (Γ := [])⟩
      (by simp [Exp.gradefree]) ⟨6, _, rfl, rfl⟩
  have w22 : SigWF (sig.take 22) :=
    .prim w21 ⟨dTyActGL w21 (decls 21 (by omega)) rfl rfl rfl rfl rfl⟩
      (by simp [Exp.gradefree]) ⟨7, _, rfl, rfl⟩
  have w23 : SigWF (sig.take 23) :=
    .prim w22 ⟨dTableA w22 (decls 22 (by omega)) rfl (Γ := [])⟩ (by simp [Exp.gradefree])
      ⟨6, _, rfl, rfl⟩
  have w24 : SigWF (sig.take 24) :=
    .prim w23 ⟨dLegal w23 rfl (Deriv.mkConst rfl (dTableA w23 (decls 23 (by omega)) rfl))
      (Γ := [])⟩ (by simp [Exp.gradefree]) ⟨7, _, rfl, rfl⟩
  have w25 : SigWF (sig.take 25) :=
    .prim w24 ⟨dLegal w24 rfl (Deriv.mkConst rfl (dTableA w24 (decls 24 (by omega)) rfl))
      (Γ := [])⟩ (by simp [Exp.gradefree]) ⟨7, _, rfl, rfl⟩
  have w26 : SigWF (sig.take 26) := .family w25 ⟨.mkTelNil⟩ (by simp)
  have w27 : SigWF (sig.take 27) :=
    .prim w26 ⟨Deriv.mkTyPi (q := .free) (dState w26 (decls 26 (by omega)) rfl rfl (Γ := []))
      (Deriv.mkTyFam w26 rfl .mkSpineNil) (by decide)⟩ (by simp [Exp.gradefree])
      ⟨25, _, rfl, rfl⟩
  have w28 : SigWF (sig.take 28) := .family w27 ⟨.mkTelNil⟩ (by simp)
  have w29 : SigWF (sig.take 29) :=
    .prim w28 ⟨Deriv.mkTyPi (q := .free) (dState w28 (decls 28 (by omega)) rfl rfl (Γ := []))
      (Deriv.mkTyFam w28 rfl .mkSpineNil) (by decide)⟩ (by simp [Exp.gradefree])
      ⟨27, _, rfl, rfl⟩
  have w30 : SigWF (sig.take 30) := .family w29 ⟨.mkTelNil⟩ (by simp)
  have w31 : SigWF (sig.take 31) := .family w30 ⟨.mkTelNil⟩ (by simp)
  have w32 : SigWF (sig.take 32) :=
    .prim w31 ⟨Deriv.mkTyPi (q := .free) (dGuardedAA w31 (decls 31 (by omega)) rfl (Γ := []))
      (Deriv.mkTyFam w31 rfl .mkSpineNil) (by decide)⟩ (by simp [Exp.gradefree])
      ⟨30, _, rfl, rfl⟩
  have w33 : SigWF (sig.take 33) :=
    .gate w32 ⟨Deriv.mkTelCons (Deriv.mkTyFam w32 rfl .mkSpineNil) .mkTelNil⟩
      ⟨Deriv.mkTyFam w32 rfl .mkSpineNil⟩ ⟨Deriv.mkTyFam w32 rfl .mkSpineNil⟩ (.inl rfl)
      (by decide) (by simp [demand]) (by decide) (by simp [Exp.gradefree])
      (by simp [Exp.gradefree]) (by simp [Exp.gradefree])
  have w34 : SigWF (sig.take 34) :=
    .attest w33 ⟨Deriv.mkApp (Deriv.mkConst rfl (Deriv.mkTyPi (q := .free)
        (dGuardedAA w33 (decls 33 (by omega)) rfl) (Deriv.mkTyFam w33 rfl .mkSpineNil)
        (by decide)))
      (Deriv.mkConst rfl (dGuardedAA w33 (decls 33 (by omega)) rfl))
      (Deriv.mkTyFam w33 rfl .mkSpineNil) (Γ := [])⟩ (by simp [Exp.IsPublic])
      (by simp [Exp.gradefree]) (.fam rfl)
  have w35 : SigWF (sig.take 35) :=
    .prim w34 ⟨Deriv.mkTyFam w34 rfl .mkSpineNil (Γ := [])⟩ (by simp [Exp.gradefree])
      ⟨29, _, rfl, rfl⟩
  exact w35

/-! ### The capture -/

theorem decls_sig : Decls sig := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The position `s₀ = (t₀, ℓ₀)`. -/
abbrev s0 : Exp := .pair (.const 22 0) (.const 23 0)
/-- `s₀' = (t₀, ℓ₁)`: the same table with its other legality proof. -/
abbrev s0' : Exp := .pair (.const 22 0) (.const 24 0)
/-- `attack s₀`, the squares White bears on. -/
abbrev atk : Exp := .app (.const 18 0) s0
/-- The certificate of the capture, `check N×e5 s₀ (attack s₀) : Applicable(N×e5, s₀)`. -/
abbrev cert : Exp := app3 (.const 19 0) nxe5 s0 atk
/-- The position after the capture, `actG N×e5 s₀ c`: the guarded action consumes
the certificate. -/
abbrev next : Exp := .pair (app3 (.const 20 0) nxe5 s0 cert) (app3 (.const 21 0) nxe5 s0 cert)
/-- The action of the declared script `id_A` on `s₀`, total on legal states. -/
abbrev actId : Exp :=
  .pair (app2 (.const 11 0) (.const 9 0) (.fst s0)) (app3 (.const 12 0) (.const 9 0) (.fst s0)
    (.snd s0))
/-- The engine's evaluation `eval s₀` and the diagram `r s₀`. -/
abbrev evalS0 : Exp := .app (.const 26 0) s0
abbrev diagram : Exp := .app (.const 28 0) s0
/-- The record of the capture, `mv N×e5 : Move`. -/
abbrev moveRec : Exp := .app (.const 31 0) nxe5
/-- The score `note(T₀; stamp(mv N×e5, e, o))`. -/
abbrev scoreT : Exp :=
  .gate 32 (.cons (.const 34 0) .nil) (.stamp moveRec (.const 33 0) (.const 33 1))
/-- Its normal form, the record: the node keeps the move and its event. -/
abbrev scoreN : Exp := .node 32 0 (.cons (.const 34 0) .nil) moveRec (.const 33 0)

/-- `⊢_S N×e5 : Guarded(A, A)`. -/
def dNxe5 {Γ : Ctx} :=
  Deriv.mkConst (i := 15) (k := 0) rfl (dGuardedAA sig_wf decls_sig rfl (Γ := Γ))

/-- `⊢_W (t₀, ℓ) : State(A)` for a legality proof `ℓ` of `t₀`. -/
def dPos (k : ℕ) (hk : sig.const? k 0 = some (.witness, legal (.const 22 0))) {Γ : Ctx} :=
  Deriv.mkPair (B := legal (.var 0))
    (Deriv.mkConst (i := 22) (k := 0) rfl (dTableA sig_wf decls_sig rfl (Γ := Γ)))
    (Deriv.mkConst hk (dLegal sig_wf rfl
      (Deriv.mkConst (i := 22) (k := 0) rfl (dTableA sig_wf decls_sig rfl))))
    (dState sig_wf decls_sig rfl rfl)

/-- `ε(s₀) = 𝟙_t₀ ⊕ 𝟙_ℓ₀`. -/
def effPos : Eff := Eff.unit (.decl 22 0) ⊓ Eff.unit (.decl 23 0)
/-- `ε(attack s₀) = 𝟙_attack ⊕ ε(s₀)`. -/
def effAtk : Eff := Eff.unit (.decl 18 0) ⊓ effPos
/-- The certificate's effect: `check`, the capture, and the effect of `attack s₀`,
which contains the position's. -/
def effCert : Eff := Eff.unit (.decl 19 0) ⊓ Eff.unit (.decl 15 0) ⊓ effAtk
/-- The effect of the position after the capture: the guarded action and the
certificate's effect. -/
def effNext : Eff := Eff.unit (.decl 20 0) ⊓ Eff.unit (.decl 21 0) ⊓ effCert
/-- `ε(eval s₀)` and `ε(r s₀)`. -/
def effEval : Eff := Eff.unit (.decl 26 0) ⊓ effPos
def effDiagram : Eff := Eff.unit (.decl 28 0) ⊓ effPos
/-- The score before contraction: `note` and `T₀` at grade `0`; the record
`mv N×e5`, the capture, the event and the origin at grade `1`. -/
def effScoreT : Eff :=
  Eff.unit (.decl 32 0) ⊓ Eff.unit (.decl 34 0) ⊓ Eff.scale .gated
    (Eff.unit (.decl 31 0) ⊓ Eff.unit (.decl 15 0) ⊓ Eff.unit (.decl 33 0) ⊓
      Eff.unit (.decl 33 1))
/-- The record: the origin is discarded. -/
def effScoreN : Eff :=
  Eff.unit (.decl 32 0) ⊓ Eff.unit (.decl 34 0) ⊓ Eff.scale .gated
    (Eff.unit (.decl 31 0) ⊓ Eff.unit (.decl 15 0) ⊓ Eff.unit (.decl 33 0))

/-- A computed effect is the effect of every derivation. -/
theorem typed_with {S : Sig} {Γ : Ctx} {ρ : Role} {t C : Exp} {E ε : Eff}
    (d : Derivable S true (.tm Γ ρ t C E)) (h : E = ε) :
    Derivable S true (.tm Γ ρ t C ε) ∧
      ∀ acc ρ' C' ε', Derivable S acc (.tm Γ ρ' t C' ε') → ε' = ε := by
  subst h
  obtain ⟨d⟩ := d
  exact ⟨⟨d⟩, fun _ _ _ _ ⟨d'⟩ => Deriv.effect_unique d' d⟩

/-- Compare two effects atom by atom. -/
macro "eff_eq" : tactic => `(tactic| (
  refine Rosette.eff_eq_of_atoms (fun i => ?_) (fun i k => ?_)
  · simp [effPos, effAtk, effCert, effNext, effEval, effDiagram, effScoreT, effScoreN,
      Eff.unit, Eff.scale]
  · simp only [effPos, effAtk, effCert, effNext, effEval, effDiagram, effScoreT, effScoreN,
      Eff.unit, Eff.scale, Pi.inf_apply, Atom.decl.injEq]
    try (split_ifs <;> simp_all [Grade.bot_eq])))

/-- `⊢_W attack`, `check`, `actG_T`, `actG_L` at their declared types. -/
def dAttackC {Γ : Ctx} :=
  Deriv.mkConst (i := 18) (k := 0) rfl (dTyAttack sig_wf decls_sig rfl rfl rfl (Γ := Γ))
def dCheckC {Γ : Ctx} :=
  Deriv.mkConst (i := 19) (k := 0) rfl (dTyCheck sig_wf decls_sig rfl rfl rfl rfl rfl (Γ := Γ))
def dActGTC {Γ : Ctx} :=
  Deriv.mkConst (i := 20) (k := 0) rfl (dTyActGT sig_wf decls_sig rfl rfl rfl rfl (Γ := Γ))
def dActGLC := Deriv.mkConst (i := 21) (k := 0) rfl (dTyActGL sig_wf decls_sig rfl rfl rfl rfl rfl)

theorem pos_typed : Derivable sig true (.tm [] .witness s0 state effPos) ∧
    ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ s0 C ε) → ε = effPos :=
  typed_with ⟨dPos 23 rfl⟩ (by eff_eq)

theorem attack_typed : Derivable sig true (.tm [] .witness atk (tbool a) effAtk) ∧
    ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ atk C ε) → ε = effAtk :=
  typed_with (Derivable.app sig_wf (.nil sig_wf) ⟨dAttackC⟩ ⟨dPos 23 rfl⟩) (by eff_eq)

/-- The certificate of the capture: `check N×e5 s₀ (attack s₀) : Applicable(N×e5, s₀)`,
whose effect has grade `0` at `check`, at the capture, at `attack`, and at `t₀`
and `ℓ₀`, and `∞` elsewhere. -/
theorem cert_typed : Derivable sig true (.tm [] .witness cert (applicable nxe5 s0) effCert) ∧
    ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ cert C ε) → ε = effCert := by
  have hΓ : CtxWF sig [] := .nil sig_wf
  exact typed_with (Derivable.app sig_wf hΓ (Derivable.app sig_wf hΓ
    (Derivable.app sig_wf hΓ ⟨dCheckC⟩ ⟨dNxe5⟩) ⟨dPos 23 rfl⟩) attack_typed.1) (by eff_eq)

/-- The position after the capture, `actG N×e5 s₀ c = (actG_T N×e5 s₀ c,
actG_L N×e5 s₀ c) : State(A)`, consumes the certificate `c`: its effect has
grade `0` at the guarded action, at the capture, at the position, and at every
atom of the certificate (`check`, `attack`), and `∞` elsewhere. -/
theorem next_typed : Derivable sig true (.tm [] .witness next state effNext) ∧
    ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ next C ε) → ε = effNext := by
  have hΓ : CtxWF sig [] := .nil sig_wf
  obtain ⟨dT⟩ := Derivable.app sig_wf hΓ (Derivable.app sig_wf hΓ
    (Derivable.app sig_wf hΓ ⟨dActGTC⟩ ⟨dNxe5⟩) ⟨dPos 23 rfl⟩) cert_typed.1
  obtain ⟨dL⟩ := Derivable.app sig_wf hΓ (Derivable.app sig_wf hΓ
    (Derivable.app sig_wf hΓ ⟨dActGLC⟩ ⟨dNxe5⟩) ⟨dPos 23 rfl⟩) cert_typed.1
  exact typed_with ⟨Deriv.mkPair (B := legal (.var 0)) dT dL
    (dState sig_wf decls_sig rfl rfl)⟩ (by eff_eq)

/-- The guard is enforced by typing: a guarded move cannot be given to the
action of declared scripts. `act_T N×e5` and `act_L N×e5` have no derivation,
raw or accepted, in any context, so the capture acts only through `actG`, which
takes its certificate. -/
theorem guarded_not_script {acc : Bool} {Γ : Ctx} {ρ : Role} {C : Exp} {ε : Eff} {k : ℕ}
    (hk : k = 11 ∨ k = 12) : ¬Derivable sig acc (.tm Γ ρ (.app (.const k 0) nxe5) C ε) := by
  rintro ⟨d⟩
  obtain ⟨q, σ, A, B, φ, η, -, -, ⟨df⟩, ⟨du⟩, -⟩ := d.inv_app
  obtain ⟨A₀, hc, hconv, -, -⟩ := df.inv_const
  obtain ⟨A₁, hc', hconv', -, -⟩ := du.inv_const
  rw [show sig.const? 15 0 = some (.script, guarded a a) from rfl] at hc'
  cases hc'
  have hdom : Conv (script a a) A := by
    rcases hk with rfl | rfl
    · rw [show sig.const? 11 0 = some (.witness, tyActT) from rfl] at hc
      cases hc
      exact (Conv.pi_inj hconv).2.2.1
    · rw [show sig.const? 12 0 = some (.witness, tyActL) from rfl] at hc
      cases hc
      exact (Conv.pi_inj hconv).2.2.1
  have := Normal.eq_of_conv (Exp.redexFree_normal rfl) (Exp.redexFree_normal rfl)
    (hconv'.trans hdom.symm)
  simp at this

/-- A declared script acts on every legal state: `act id_A s₀ =
(act_T id_A (fst s₀), act_L id_A (fst s₀) (snd s₀)) : State(A)`. Its effect has
no certificate in it. -/
theorem actId_typed : ∃ ε, Derivable sig true (.tm [] .witness actId state ε) ∧
    ε (.decl 19 0) = .absent ∧ ε (.decl 18 0) = .absent := by
  have hΓ : CtxWF sig [] := .nil sig_wf
  have hid : Derivable sig true (.tm [] .script (.const 9 0) (script a a) _) :=
    ⟨Deriv.mkConst (i := 9) (k := 0) rfl (dScriptAA sig_wf decls_sig rfl)⟩
  have hfst : Derivable sig true (.tm [] .witness (.fst s0) (table a) _) :=
    ⟨Deriv.mkFst (dPos 23 rfl) (dTableA sig_wf decls_sig rfl)⟩
  have hsnd : Derivable sig true (.tm [] .witness (.snd s0) (legal (.fst s0)) _) :=
    ⟨Deriv.mkSnd (dPos 23 rfl) (dLegal sig_wf rfl (Deriv.mkFst (dPos 23 rfl)
      (dTableA sig_wf decls_sig rfl)))⟩
  obtain ⟨dT⟩ := Derivable.app sig_wf hΓ (Derivable.app sig_wf hΓ
    ⟨Deriv.mkConst (i := 11) (k := 0) rfl (dTyActT sig_wf decls_sig rfl rfl)⟩ hid) hfst
  obtain ⟨dL⟩ := Derivable.app sig_wf hΓ (Derivable.app sig_wf hΓ (Derivable.app sig_wf hΓ
    ⟨Deriv.mkConst (i := 12) (k := 0) rfl (dTyActL sig_wf decls_sig rfl rfl rfl rfl)⟩ hid)
    hfst) hsnd
  exact ⟨_, ⟨Deriv.mkPair (B := legal (.var 0)) dT dL (dState sig_wf decls_sig rfl rfl)⟩,
    by simp [Eff.unit, Eff.scale, Grade.top_eq], by simp [Eff.unit, Eff.scale, Grade.top_eq]⟩

/-- The engine's evaluation and the diagram are renderings of the position:
`⊢_R eval s₀ : Num` and `⊢_R r s₀ : Graphic`. -/
theorem readings_typed :
    (Derivable sig true (.tm [] .rendering evalS0 num effEval) ∧
      ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ evalS0 C ε) → ε = effEval) ∧
    (Derivable sig true (.tm [] .rendering diagram graphic effDiagram) ∧
      ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ diagram C ε) → ε = effDiagram) := by
  have hΓ : CtxWF sig [] := .nil sig_wf
  refine ⟨typed_with (Derivable.app sig_wf hΓ ⟨Deriv.mkConst (i := 26) (k := 0) rfl
      (Deriv.mkTyPi (q := .free) (dState sig_wf decls_sig rfl rfl)
        (Deriv.mkTyFam sig_wf rfl .mkSpineNil) (by decide))⟩ ⟨dPos 23 rfl⟩) (by eff_eq),
    typed_with (Derivable.app sig_wf hΓ ⟨Deriv.mkConst (i := 28) (k := 0) rfl
      (Deriv.mkTyPi (q := .free) (dState sig_wf decls_sig rfl rfl)
        (Deriv.mkTyFam sig_wf rfl .mkSpineNil) (by decide))⟩ ⟨dPos 23 rfl⟩) (by eff_eq)⟩

/-- `⊢_W mv N×e5 : Move`, the record of the capture. -/
def dMoveRec {Γ : Ctx} :=
  Deriv.mkApp (Deriv.mkConst (i := 31) (k := 0) rfl (Deriv.mkTyPi (q := .free)
      (dGuardedAA sig_wf decls_sig rfl (Γ := Γ)) (Deriv.mkTyFam sig_wf rfl .mkSpineNil)
      (by decide)))
    dNxe5 (Deriv.mkTyFam sig_wf rfl .mkSpineNil)

/-- `⊢_W stamp(mv N×e5, e, o) : Stamped_W(Move)`, from the attestation. -/
def dStampRec {Γ : Ctx} :=
  Deriv.mkStamp (dMoveRec (Γ := Γ)) (Deriv.mkConst (i := 33) (k := 0) rfl .mkTyEvent)
    (Deriv.mkConst (i := 33) (k := 1) rfl (Deriv.mkTyOrigin (by decide)
      (Deriv.mkTyFam sig_wf rfl .mkSpineNil) (Deriv.mkConst (i := 33) (k := 0) rfl .mkTyEvent)
      dMoveRec))
    (Deriv.mkTyStamped (Deriv.mkTyFam sig_wf rfl .mkSpineNil) (by decide))

/-- The score keeps the capture through the gate. `note(T₀; stamp(mv N×e5, e, o))`
has type `Score` at the form role; it contracts in one record step to the node
`note_0(T₀; mv N×e5, e)`, a normal form that retains the move and its event.
Both effects have grade `1` at the capture and at its record: the score depends
on the capture only through the gate. -/
theorem score_typed :
    (Derivable sig true (.tm [] .form scoreT score effScoreT) ∧
      ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ scoreT C ε) → ε = effScoreT) ∧
    (Derivable sig true (.tm [] .form scoreN score effScoreN) ∧
      ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ scoreN C ε) → ε = effScoreN) ∧
    Step scoreT scoreN ∧ Normal scoreN ∧ Exp.const 33 0 ∈ scoreN.events ∧
    effScoreT (.decl 15 0) = .gated ∧ effScoreN (.decl 15 0) = .gated := by
  have dds : Deriv sig true (.spine [] (.cons (.const 34 0) .nil) [(.form, score)] _) :=
    Deriv.mkSpineCons (Δ := []) (Deriv.mkConst (i := 34) (k := 0) rfl
      (Deriv.mkTyFam sig_wf rfl .mkSpineNil)) .mkSpineNil
  refine ⟨typed_with ⟨Deriv.mkGate sig_wf (g := 32) rfl dds dStampRec
      (Deriv.mkTyFam sig_wf rfl .mkSpineNil)⟩ (by eff_eq),
    typed_with ⟨Deriv.mkNode (ℓ := 0) sig_wf (g := 32) rfl dds dMoveRec
      (Deriv.mkConst (i := 33) (k := 0) rfl .mkTyEvent)
      (Deriv.mkTyFam sig_wf rfl .mkSpineNil)⟩ (by eff_eq),
    .record, Exp.redexFree_normal rfl, by simp [Exp.events], ?_, ?_⟩ <;>
  simp [effScoreT, effScoreN, Eff.unit, Eff.scale]

/-- The rendering firewall (`sec:firewall`) and the readback variant of `prop:chess`. Every
term of the capture signature at a non-rendering role, in the empty context, has
grade `∞` at the evaluation and the diagram: no certificate, position or score
uses them. A certificate family indexed by the evaluation's type is rejected by
Sig-Family, since its formation edge from a rendering into the witness role has
demand `∞`. A function type with a rendering domain at a non-rendering role has
grade `∞`; a stamp cannot carry a rendering; every gate targets the form or the
presentation role. -/
theorem firewall :
    (∀ {ρ : Role} {t C : Exp} {ε : Eff}, ρ ≠ .rendering →
      Deriv sig true (.tm [] ρ t C ε) →
        ε (.decl 26 0) = .absent ∧ ε (.decl 28 0) = .absent) ∧
    ¬SigWF (sig ++ [.family [(.rendering, num)] .witness]) ∧
    (∀ {acc : Bool} {Γ : Ctx} {ρ : Role} {q : Grade} {A B : Exp} {α : Eff},
      ρ ≠ .rendering → Deriv sig acc (.ty Γ ρ (.pi q .rendering A B) α) → q = .absent) ∧
    (∀ {acc : Bool} {Γ : Ctx} {ρ : Role} {A : Exp} {α : Eff},
      ¬Nonempty (Deriv sig acc (.ty Γ ρ (.stamped .rendering A) α))) ∧
    (∀ {g : ℕ} {Δ : Tel} {σ ρ : Role} {A B : Exp}, sig.gate? g = some (Δ, σ, A, ρ, B) →
      ρ = .form ∨ ρ = .presentation) := by
  have hR : ∀ {ρ : Role}, ρ ≠ .rendering → demand .rendering ρ = .absent := fun {ρ} hρ => by
    cases ρ <;> first | rfl | exact absurd rfl hρ
  refine ⟨fun {ρ t C ε} hρ d => ?_, fun h => ?_, fun {acc Γ ρ q A B α} hρ d => ?_,
    fun {acc Γ ρ A α} ⟨d⟩ => d.inv_tyStamped.2.1 rfl, fun h => (sig_wf.gate_cond h).2.1⟩
  · have h26 := d.valid_tm (.decl 26 0) .rendering rfl
    have h28 := d.valid_tm (.decl 28 0) .rendering rfl
    rw [hR hρ] at h26 h28
    exact ⟨top_unique h26, top_unique h28⟩
  · have := h.family_demand (a := 35) rfl (.rendering, num) (by simp)
    simp [demand] at this
  · have := d.tyPi_demand
    rw [hR hρ] at this
    exact top_unique this

/-- The silent-score variant of `prop:chess`. Every term at the form or the
presentation role has grade at least `1` at the capture: a score uses the
capture only through a gate. A primitive that would compute a score from a
guarded move is rejected by Sig-Primitive, at every grade: at grade `0` its
binder check fails, since the capture's role demands `1` of the form role, and
at any other grade it is not grade-free. -/
theorem silent_score :
    (∀ {ρ : Role} {t C : Exp} {ε : Eff}, (ρ = .form ∨ ρ = .presentation) →
      Deriv sig true (.tm [] ρ t C ε) → .gated ≤ ε (.decl 15 0)) ∧
    ∀ q, ¬SigWF (sig ++ [.prim .form (.pi q .script (guarded a a) score)]) := by
  refine ⟨fun {ρ t C ε} hρ d => ?_, fun q h => ?_⟩
  · have := d.valid_tm (.decl 15 0) .script rfl
    rcases hρ with rfl | rfl <;> exact this
  · obtain ⟨⟨α, ⟨d⟩⟩, hgf⟩ := sigWF_last_prim h
    obtain ⟨rfl, -⟩ := hgf
    exact absurd d.tyPi_demand (by decide)

/-- `State(A)` counts legality proofs (`sec:frames-calculus` and Astra's finding 2). Two
legality proofs `ℓ₀`, `ℓ₁` of the same table `t₀` give two states that are
distinct normal forms, not definitionally equal, with the same table. -/
theorem two_legal_states :
    Derivable sig true (.tm [] .witness s0 state effPos) ∧
    Derivable sig true (.tm [] .witness s0' state
      (Eff.unit (.decl 22 0) ⊓ Eff.unit (.decl 24 0))) ∧
    Normal s0 ∧ Normal s0' ∧ ¬Conv s0 s0' ∧ Conv (.fst s0) (.fst s0') :=
  ⟨pos_typed.1, ⟨dPos 24 rfl⟩, Exp.redexFree_normal rfl, Exp.redexFree_normal rfl,
    fun hc => by
      have := Normal.eq_of_conv (Exp.redexFree_normal rfl) (Exp.redexFree_normal rfl) hc
      simp at this,
    Conv.trans (Relation.EqvGen.rel _ _ Step.fstPair)
      (Conv.symm (Relation.EqvGen.rel _ _ Step.fstPair))⟩

/-- The frame enters through types. The addressing is declared at
`Addr(Board)`, whose formation effect has grade `0` at the board's constants;
the formation effects of `State(A)`, `Table_Bool(A)` and `Guarded(A, A)`, the
types of the position, of the squares White bears on and of the capture, have
grade `0` at the addressing. -/
theorem frame_types :
    sig.const? 5 0 = some (.presentation, addr board) ∧
    (∀ acc Γ ρ α, Derivable sig acc (.ty Γ ρ (addr board) α) →
      α = Eff.unit (.decl 4 0) ⊓ ((Eff.unit (.decl 2 0) ⊓ Eff.unit (.decl 3 0)) ⊓ ⊤)) ∧
    (∀ acc Γ ρ α, Derivable sig acc (.ty Γ ρ state α) → α (.decl 5 0) = .free) ∧
    (∀ acc Γ ρ α, Derivable sig acc (.ty Γ ρ (tbool a) α) → α (.decl 5 0) = .free) ∧
    (∀ acc Γ ρ α, Derivable sig acc (.ty Γ ρ (guarded a a) α) → α (.decl 5 0) = .free) := by
  refine ⟨rfl, fun acc Γ ρ α ⟨d⟩ => ?_, fun acc Γ ρ α ⟨d⟩ => ?_, fun acc Γ ρ α ⟨d⟩ => ?_,
    fun acc Γ ρ α ⟨d⟩ => ?_⟩
  · rw [Deriv.ty_effect_unique _ d (dAddr sig_wf rfl (dCode sig_wf rfl rfl rfl rfl) (Γ := Γ))]
  · rw [Deriv.ty_effect_unique _ d (dState sig_wf decls_sig rfl rfl (Γ := Γ))]
    simp [Eff.unit, Eff.unbind, Grade.bot_eq]
  · rw [Deriv.ty_effect_unique _ d (dFam1 sig_wf (k := 17) rfl (dA' sig_wf decls_sig (Γ := Γ)))]
    simp [Eff.unit, Grade.bot_eq]
  · rw [Deriv.ty_effect_unique _ d (dGuardedAA sig_wf decls_sig rfl (Γ := Γ))]
    simp [Eff.unit, Grade.bot_eq]

/-- The derivations' effects realize the edges of the capture's construction
(`tab:chess`) into its terms, item for item. An effect `ε_u ≤ ε_v` says that
`u` uses every atom of `v` at grade `0`; `ε_u ≤ 1 ⊗ ε_v` says at grade at most
`1`. The squares White bears on use the position; the certificate uses the
position, the squares White bears on and the capture; the position after the
capture uses the position, the capture and the certificate; the score uses the
capture through the gate, and not at grade `0`; the evaluation and the diagram
use the position; neither the certificate nor the position after uses the
evaluation. -/
theorem effects_match_table :
    effAtk ≤ effPos ∧
    effCert ≤ effPos ∧ effCert ≤ effAtk ∧ effCert ≤ Eff.unit (.decl 15 0) ∧
    effNext ≤ effPos ∧ effNext ≤ Eff.unit (.decl 15 0) ∧ effNext ≤ effCert ∧
    effScoreT ≤ Eff.scale .gated (Eff.unit (.decl 15 0)) ∧
      ¬effScoreT ≤ Eff.unit (.decl 15 0) ∧
    effEval ≤ effPos ∧ effDiagram ≤ effPos ∧
    effCert (.decl 26 0) = .absent ∧ effNext (.decl 26 0) = .absent := by
  refine ⟨inf_le_right, ?_, inf_le_right, ?_, ?_, ?_, inf_le_right, ?_, fun h => ?_,
    inf_le_right, inf_le_right, by simp [effCert, effAtk, effPos, Eff.unit, Grade.top_eq],
    by simp [effNext, effCert, effAtk, effPos, Eff.unit, Grade.top_eq]⟩
  · exact inf_le_right.trans inf_le_right
  · exact inf_le_left.trans inf_le_right
  · exact (inf_le_right.trans inf_le_right).trans inf_le_right
  · exact inf_le_right.trans (inf_le_left.trans inf_le_right)
  · exact inf_le_right.trans
      (Eff.scale_mono le_rfl ((inf_le_left.trans inf_le_left).trans inf_le_right))
  · have := h (.decl 15 0)
    simp [effScoreT, Eff.unit, Eff.scale] at this

/-- Outside the bidirectional fragment the reference procedure is incomplete
(`prop:checker` holds for the fragment): `fst s₀` is derivable at `Table(A)`,
but its argument is a pair, which has no synthesized type, so the checker
rejects the judgment. -/
theorem checker_incomplete :
    Derivable sig true (.tm [] .witness (.fst s0) (table a) effPos) ∧
    ∀ hC, check sig_wf [] (.nil sig_wf) (.fst s0) .witness (table a) hC = none :=
  ⟨⟨Deriv.mkFst (dPos 23 rfl) (dTableA sig_wf decls_sig rfl)⟩,
    fun hC => check_fst_pair sig_wf (.nil sig_wf) _ _ hC⟩

/-! ### The capture of `tab:chess`, read off the derivations

Part I's construction `Artform.Roles.chess` lists the items of the capture with
their roles and direct dependencies (`tab:chess`). Here each item is a closed
term of the capture signature, typed at its role. An item `v` uses an item `u`
at the least grade at which the effect of `v`'s term, or the formation effect
of `v`'s type, uses a declaration of `u`. Effects are path closed
(`Deriv.eff_eq_pathEff`), so the uses include some chains of the table as
single steps, and the table writes some chains through the frame as single
steps; the two have the same live chains at every grade. -/

open Artform.Roles (ChessItem)

/-- The closed term of the capture signature for each item of `tab:chess`. -/
def itemTerm : ChessItem → Exp
  | .board => board
  | .addressing => a
  | .position => s0
  | .attackMap => atk
  | .certificate => cert
  | .capture => nxe5
  | .next => next
  | .score => scoreT
  | .evaluation => evalS0
  | .diagram => diagram

/-- The type of each item. -/
def itemType : ChessItem → Exp
  | .board => form
  | .addressing => addr board
  | .position => state
  | .attackMap => tbool a
  | .certificate => applicable nxe5 s0
  | .capture => guarded a a
  | .next => state
  | .score => score
  | .evaluation => num
  | .diagram => graphic

/-- The declarations that each item adds to the signature. -/
def own : ChessItem → List Atom
  | .board => [.decl 2 0, .decl 3 0]
  | .addressing => [.decl 5 0]
  | .position => [.decl 22 0, .decl 23 0]
  | .attackMap => [.decl 18 0]
  | .certificate => [.decl 19 0]
  | .capture => [.decl 15 0]
  | .next => [.decl 20 0, .decl 21 0]
  | .score => [.decl 32 0, .decl 34 0]
  | .evaluation => [.decl 26 0]
  | .diagram => [.decl 28 0]

/-- The effect of each item's term. -/
def termEff : ChessItem → Eff
  | .board => Eff.unit (.decl 2 0) ⊓ Eff.unit (.decl 3 0)
  | .addressing => Eff.unit (.decl 5 0)
  | .position => effPos
  | .attackMap => effAtk
  | .certificate => effCert
  | .capture => Eff.unit (.decl 15 0)
  | .next => effNext
  | .score => effScoreT
  | .evaluation => effEval
  | .diagram => effDiagram

/-- The formation effect of each item's type. -/
def typeEff : ChessItem → Eff
  | .board => Eff.unit (.decl 0 0) ⊓ ⊤ ⊓ (Eff.unit (.decl 1 0) ⊓ (Eff.unit (.var 0) ⊓ ⊤)).unbind
  | .addressing => Eff.unit (.decl 4 0) ⊓ ((Eff.unit (.decl 2 0) ⊓ Eff.unit (.decl 3 0)) ⊓ ⊤)
  | .position | .next =>
    Eff.unit (.decl 6 0) ⊓ (Eff.unit (.decl 5 0) ⊓ ⊤) ⊓
      (Eff.unit (.decl 7 0) ⊓ (Eff.unit (.var 0) ⊓ ⊤)).unbind
  | .attackMap => Eff.unit (.decl 17 0) ⊓ (Eff.unit (.decl 5 0) ⊓ ⊤)
  | .certificate => Eff.unit (.decl 16 0) ⊓ (Eff.unit (.decl 15 0) ⊓ (effPos ⊓ ⊤))
  | .capture => Eff.unit (.decl 14 0) ⊓ (Eff.unit (.decl 5 0) ⊓ (Eff.unit (.decl 5 0) ⊓ ⊤))
  | .score => Eff.unit (.decl 29 0) ⊓ ⊤
  | .evaluation => Eff.unit (.decl 25 0) ⊓ ⊤
  | .diagram => Eff.unit (.decl 27 0) ⊓ ⊤

/-- Each item of `tab:chess` is a closed term of the capture signature, typed at
the role that the table gives it; its term and its type have the effects
`termEff` and `typeEff` in every derivation. -/
theorem items_typed (v : ChessItem) :
    Derivable sig true (.tm [] v.role (itemTerm v) (itemType v) (termEff v)) ∧
    (∀ acc ρ C ε, Derivable sig acc (.tm [] ρ (itemTerm v) C ε) → ε = termEff v) ∧
    (∀ acc ρ α, Derivable sig acc (.ty [] ρ (itemType v) α) → α = typeEff v) := by
  have ty : ∀ {T : Exp} {ρ₀ : Role} {α₀ : Eff}, Deriv sig true (.ty [] ρ₀ T α₀) →
      ∀ acc ρ α, Derivable sig acc (.ty [] ρ T α) → α = α₀ :=
    fun d₀ _ _ _ ⟨d⟩ => Deriv.ty_effect_unique _ d d₀
  have tm : ∀ {t T : Exp} {ρ₀ : Role} {ε₀ : Eff}, Deriv sig true (.tm [] ρ₀ t T ε₀) →
      ∀ acc ρ C ε, Derivable sig acc (.tm [] ρ t C ε) → ε = ε₀ :=
    fun d₀ _ _ _ _ ⟨d⟩ => Deriv.effect_unique d d₀
  cases v
  · exact ⟨⟨dCode sig_wf rfl rfl rfl rfl⟩, tm (dCode sig_wf rfl rfl rfl rfl),
      ty (Book.dForm sig_wf rfl rfl)⟩
  · exact ⟨⟨dA' sig_wf decls_sig⟩, tm (dA' sig_wf decls_sig),
      ty (dAddr sig_wf rfl (dCode sig_wf rfl rfl rfl rfl))⟩
  · exact ⟨pos_typed.1, pos_typed.2, ty (dState sig_wf decls_sig rfl rfl)⟩
  · exact ⟨attack_typed.1, attack_typed.2,
      ty (dFam1 sig_wf (k := 17) rfl (dA' sig_wf decls_sig))⟩
  · exact ⟨cert_typed.1, cert_typed.2, ty (dApplicable sig_wf rfl dNxe5 (dPos 23 rfl))⟩
  · exact ⟨⟨dNxe5⟩, tm dNxe5, ty (dGuardedAA sig_wf decls_sig rfl)⟩
  · exact ⟨next_typed.1, next_typed.2, ty (dState sig_wf decls_sig rfl rfl)⟩
  · exact ⟨score_typed.1.1, score_typed.1.2, ty (Deriv.mkTyFam sig_wf (a := 29) rfl .mkSpineNil)⟩
  · exact ⟨readings_typed.1.1, readings_typed.1.2,
      ty (Deriv.mkTyFam sig_wf (a := 25) rfl .mkSpineNil)⟩
  · exact ⟨readings_typed.2.1, readings_typed.2.2,
      ty (Deriv.mkTyFam sig_wf (a := 27) rfl .mkSpineNil)⟩

/-- The grade at which item `v` uses item `u`: the least grade, in the effect of
`v`'s term and the formation effect of `v`'s type, at a declaration of `u`. -/
def uses (u v : ChessItem) : Grade :=
  if u = v then .absent else ((own u).map (termEff v ⊓ typeEff v)).foldr (· ⊓ ·) ⊤

/-- The uses, as a table: the addressing is used by the items whose types are
indexed by it, and the position after the capture uses the squares White bears
on inside its certificate. -/
def usesTable : ChessItem → ChessItem → Grade
  | .board, .addressing => .free
  | .addressing, .position => .free
  | .addressing, .attackMap => .free
  | .addressing, .capture => .free
  | .addressing, .next => .free
  | .position, .attackMap => .free
  | .position, .certificate => .free
  | .position, .next => .free
  | .position, .evaluation => .free
  | .position, .diagram => .free
  | .attackMap, .certificate => .free
  | .attackMap, .next => .free
  | .capture, .certificate => .free
  | .capture, .next => .free
  | .capture, .score => .gated
  | .certificate, .next => .free
  | _, _ => .absent

/-- The uses read off the effects are the table, item for item. -/
theorem uses_eq (u v : ChessItem) : uses u v = usesTable u v := by
  revert u v
  decide

/-- The construction read off the derivations of the capture signature. -/
def readOff : Artform.Roles.Construction ChessItem := ⟨Artform.Roles.ChessItem.role, uses⟩

theorem readOff_valid : readOff.Valid demand := by
  intro u v
  rw [show readOff.edge u v = usesTable u v from uses_eq u v]
  revert u v
  decide

/-- **The capture, once** (`sec:capture`, `tab:chess`). The construction read off
the derivations of the capture signature has the roles of `tab:chess` and the
same live chains as `Artform.Roles.chess`, at every grade. -/
theorem read_off_reach (g : Grade) (u v : ChessItem) :
    readOff.Reach g u v ↔ Artform.Roles.chess.Reach g u v := by
  have total : ∀ {c : Artform.Roles.Construction ChessItem} (u v : ChessItem),
      c.Reach .absent u v := fun u v => .one (le_top.trans_eq Grade.top_eq)
  cases g
  case absent => exact ⟨fun _ => total u v, fun _ => total u v⟩
  all_goals refine ⟨.of_edges fun u v h => ?_, .of_edges fun u v h => ?_⟩
  all_goals
    revert h
    cases u <;> cases v <;> intro h
  all_goals first
    | exact absurd h (by decide)
    | exact .one (by decide)
    | exact .two (w := .addressing) (by decide) (by decide)
    | exact .two (w := .position) (by decide) (by decide)
    | exact .two (w := .certificate) (by decide) (by decide)

end Chess

end Book

end Artform.Roles.Calculus
