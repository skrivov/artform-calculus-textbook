import ArtformScores.NonabelianGravity.Maurer
import ArtformScores.NonabelianGravity.Dynamics

/-! # NGB: the formal word compiler evaluates to the actual group processes -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Maurer
variable {G : Type} [Group G]
def evalLetter (g : ℕ → G) (a : Letter) : G := if a.2 then g a.1 else (g a.1)⁻¹
def evalWord (g : ℕ → G) (w : Word) : G := (w.map (evalLetter g)).prod
lemma eval_append (g : ℕ → G) (u v : Word) :
    evalWord g (u++v)=evalWord g u*evalWord g v := by simp [evalWord]
lemma eval_inverseLetter (g : ℕ → G) (a : Letter) :
    evalLetter g (inverseLetter a)=(evalLetter g a)⁻¹ := by
  rcases a with ⟨i,b⟩
  cases b <;> simp [inverseLetter,evalLetter]
lemma eval_wi (g : ℕ → G) (w : Word) : evalWord g (wi w)=(evalWord g w)⁻¹ := by
  induction w with
  | nil => simp [wi,evalWord]
  | cons a w ih =>
    simp only [wi,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      evalWord,List.map_cons,List.map_nil,List.prod_cons,
      eval_inverseLetter,mul_inv_rev,List.prod_append] at ih ⊢
    rw [ih]
    simp
lemma eval_reduceStep (g : ℕ → G) (w : Word) (a : Letter) :
    evalWord g ((reduceStep w a).reverse)=evalWord g w.reverse*evalLetter g a := by
  cases w with
  | nil => simp [reduceStep,evalWord]
  | cons b bs =>
    by_cases hb : b=inverseLetter a
    · subst b
      simp [reduceStep,evalWord,eval_inverseLetter,mul_assoc]
    · simp [reduceStep,hb,evalWord,mul_assoc]
lemma eval_reduceAux (g : ℕ → G) (w stack : Word) :
    evalWord g ((w.foldl reduceStep stack).reverse)=evalWord g stack.reverse*evalWord g w := by
  induction w generalizing stack with
  | nil => simp [evalWord]
  | cons a w ih =>
    rw [List.foldl_cons,ih,eval_reduceStep]
    simp [evalWord,mul_assoc]
lemma eval_wm (g : ℕ → G) (u v : Word) : evalWord g (wm u v)=evalWord g u*evalWord g v := by
  simpa [wm,reduceWord,evalWord] using eval_reduceAux g (u++v) []
lemma eval_product_aux (g : ℕ → G) (ws : List Word) (acc : Word) :
    evalWord g (ws.foldl wm acc)=evalWord g acc*(ws.map (evalWord g)).prod := by
  induction ws generalizing acc with
  | nil => simp
  | cons w ws ih => simp [List.foldl_cons,ih,eval_wm,mul_assoc]
lemma eval_product (g : ℕ → G) (ws : List Word) :
    evalWord g (product ws)=(ws.map (evalWord g)).prod := by
  simpa [product,evalWord] using eval_product_aux g ws []
def evalState (g : ℕ → G) (s : State Word) : State G :=
  ⟨fun e => evalWord g (s.U e),fun e => evalWord g (s.P e)⟩
lemma eval_holonomy (g : ℕ → G) (s : State Word) (f : canvas.F) (i : Fin 4) :
    evalWord g (holonomyWord s f i)=holonomy (evalState g s).U f i := by
  simp only [holonomyWord,eval_product,List.map_reverse,List.map_map,holonomy]
  congr 2
  apply List.map_congr_left
  intro a _
  rcases a with ⟨e,b⟩
  cases b <;> simp [eval_wi,evalState]
lemma eval_wordLeft (g : ℕ → G) (s : State Word) (f : canvas.F) (e : canvas.E) :
    evalWord g (wordLeft f s e)=leftFactor f false (evalState g s).U e := by
  by_cases hf : f=0
  · fin_cases e <;> simp only [wordLeft,leftFactor,ite_eq_left hf]
    · exact eval_holonomy g s f 0
    · exact eval_holonomy g s f 1
    · exact eval_holonomy g s f 2
    · exact eval_holonomy g s f 3
    all_goals rfl
  · fin_cases e <;> simp only [wordLeft,leftFactor,ite_eq_right hf]
    all_goals first
    | rfl
    | exact eval_holonomy g s f 0
    | exact eval_holonomy g s f 1
    | exact eval_holonomy g s f 2
lemma eval_wordRight (g : ℕ → G) (s : State Word) (f : canvas.F) (e : canvas.E) :
    evalWord g (wordRight f s e)=rightFactor f false (evalState g s).U e := by
  by_cases hf : f=0
  · simp [wordRight,rightFactor,hf,evalWord]
  · by_cases he : e=1
    · subst e
      simp only [wordRight,rightFactor,ite_eq_right hf]
      change evalWord g (wm (wm (s.U 1) (wi (holonomyWord s f 3))) (wi (s.U 1)))=
        evalWord g (s.U 1)*(holonomy (evalState g s).U f 3)⁻¹*(evalWord g (s.U 1))⁻¹
      rw [eval_wm,eval_wm,eval_wi,eval_wi,eval_holonomy]
    · fin_cases e <;> simp_all [wordRight,rightFactor,evalWord]
lemma eval_wordKick (g : ℕ → G) (s : State Word) (f : canvas.F) :
    evalState g (wordKick f s)=kick f false (evalState g s) := by
  apply State.ext
  · rfl
  · funext e
    change evalWord g (wm (wm (wordLeft f s e) (s.P e)) (wordRight f s e))=
      leftFactor f false (evalState g s).U e*evalWord g (s.P e)*
        rightFactor f false (evalState g s).U e
    rw [eval_wm,eval_wm,eval_wordLeft,eval_wordRight]
lemma eval_wordDrift (g : ℕ → G) (s : State Word) :
    evalState g (wordDrift s)=drift false (evalState g s) := by
  apply State.ext
  · funext e
    exact eval_wm g _ _
  · rfl

def assignment (s : State G) (i : ℕ) : G :=
  if h : i<7 then s.U ⟨i,h⟩ else if h : i<14 then s.P ⟨i-7,by omega⟩ else 1
lemma eval_original (s : State G) : evalState (assignment s) original=s := by
  apply State.ext <;> funext e <;> fin_cases e <;>
    simp [evalState,original,variableWord,evalWord,evalLetter,assignment]

/-! ## Non-vacuity -/
example (g : ℕ → G) : (evalState g original).U 0=g 0 := by
  simp [evalState,original,variableWord,evalWord,evalLetter]
end Artform.Scores.NonabelianGravity.Maurer
