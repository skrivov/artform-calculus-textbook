import ArtformScores.NonabelianGravity.Geometry

/-! # NGB: finite formal Maurer-Cartan two-form certificates

Words are reduced by adjacent inverse cancellation. A one-form term is a
coefficient times Ad(word) applied to one named right Maurer form. Pairing
invariance expands a wedge into two ordered bilinear terms. All results here
are identities of that finite algebra, not a manifold or reduction theorem.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace Artform.Scores.NonabelianGravity.Maurer
abbrev Letter := ℕ × Bool
abbrev Word := List Letter
def inverseLetter (a : Letter) : Letter := (a.1,!a.2)
def reduceStep (stack : Word) (a : Letter) : Word :=
  match stack with
  | [] => [a]
  | b::bs => if b=inverseLetter a then bs else a::stack
def reduceWord (w : Word) : Word := (w.foldl reduceStep []).reverse
def wm (u v : Word) : Word := reduceWord (u++v)
def wi (w : Word) : Word := w.reverse.map inverseLetter
def variableWord (i : ℕ) : Word := [(i,true)]

abbrev OneTerm := ℤ × (ℕ × Word)
abbrev OneForm := List OneTerm
abbrev Key := ℕ × ℕ × Word
abbrev Term := ℤ × Key
abbrev TwoForm := List Term
def ad (w : Word) (a : OneForm) : OneForm :=
  a.map (fun t => (t.1,t.2.1,wm w t.2.2))
def rightAux (cur : Word) : Word → OneForm
  | [] => []
  | a::rest =>
      (if a.2 then (1,a.1,cur) else (-1,a.1,wm cur [a]))::
        rightAux (wm cur [a]) rest
def right (w : Word) : OneForm := rightAux [] w
def left (w : Word) : OneForm := ad (wi w) (right w)
def wedge (a b : OneForm) : TwoForm := a.flatMap fun x => b.flatMap fun y =>
  [(x.1*y.1,x.2.1,y.2.1,wm (wi x.2.2) y.2.2),
   (-(x.1*y.1),y.2.1,x.2.1,wm (wi y.2.2) x.2.2)]
def negative (a : TwoForm) : TwoForm := a.map fun t => (-t.1,t.2)
def insert (x : Term) : TwoForm → TwoForm
  | [] => if x.1=0 then [] else [x]
  | y::ys => if x.1=0 then y::ys else if x.2=y.2 then
      if x.1+y.1=0 then ys else (x.1+y.1,x.2)::ys
    else y::insert x ys
def collect (a : TwoForm) : TwoForm := a.foldl (fun acc x => insert x acc) []

def original : State Word :=
  ⟨fun e => variableWord e.val,fun e => variableWord (7+e.val)⟩
def outgoingWord (s : State Word) (e : canvas.E) : Word :=
  wm (wm (wi (s.U e)) (wi (s.P e))) (s.U e)
def product (ws : List Word) : Word := ws.foldl wm []
def holonomyWord (s : State Word) (f : canvas.F) (i : Fin 4) : Word :=
  product (((basedLoop f i).map fun a => if a.2 then s.U a.1 else wi (s.U a.1)).reverse)
def wordLeft (f : canvas.F) (s : State Word) : canvas.E → Word :=
  let k := holonomyWord s f
  if f=0 then ![k 0,k 1,k 2,k 3,[],[],[]] else ![[],[],[],[],k 0,k 1,k 2]
def wordRight (f : canvas.F) (s : State Word) : canvas.E → Word :=
  if f=0 then fun _ => []
  else ![[],wm (wm (s.U 1) (wi (holonomyWord s f 3))) (wi (s.U 1)),[],[],[],[],[]]
def wordKick (f : canvas.F) (s : State Word) : State Word :=
  ⟨s.U,fun e => wm (wm (wordLeft f s e) (s.P e)) (wordRight f s e)⟩
def wordDrift (s : State Word) : State Word := ⟨fun e => wm (s.P e) (s.U e),s.P⟩
def edgeForm (s : State Word) (e : canvas.E) : TwoForm :=
  let a := s.U e
  let b := wm (wi a) (s.P e)
  wedge (left a) (right b) ++ wedge (right a) (left b)
def fusion (s : State Word) (v : canvas.V) : TwoForm :=
  ((star v).foldl (fun (acc : Word × TwoForm) a =>
    let m := if a.2 then s.P a.1 else outgoingWord s a.1
    (wm acc.1 m,acc.2++wedge (left acc.1) (right m))) (([] : Word),([] : TwoForm))).2
/-- Twice the AMM edge sum and ordered fusion form, expanded in formal bilinear keys. -/
def twiceOmega (s : State Word) : TwoForm :=
  (List.finRange 7).flatMap (edgeForm s) ++ (List.finRange 6).flatMap (fusion s)
def defect (f : State Word → State Word) : TwoForm :=
  twiceOmega (f original) ++ negative (twiceOmega original)

set_option maxHeartbeats 4000000 in
-- The kernel evaluates the complete finite word and coefficient certificate.
lemma face0_normal : collect (defect (wordKick 0))=[] := by decide +kernel
set_option maxHeartbeats 4000000 in
-- The kernel evaluates the complete finite word and coefficient certificate.
lemma face1_normal : collect (defect (wordKick 1))=[] := by decide +kernel
set_option maxHeartbeats 4000000 in
-- The kernel evaluates the complete finite word and coefficient certificate.
lemma drift_normal : collect (defect wordDrift)=[] := by decide +kernel

variable {R : Type*} [CommRing R]
def value (pair : Key → R) (a : TwoForm) : R :=
  (a.map (fun t => (t.1 : R)*pair t.2)).sum
lemma value_cons (pair : Key → R) (x : Term) (a : TwoForm) :
    value pair (x::a)=(x.1 : R)*pair x.2+value pair a := rfl
lemma value_insert (pair : Key → R) (x : Term) (a : TwoForm) :
    value pair (insert x a)=(x.1 : R)*pair x.2+value pair a := by
  induction a with
  | nil =>
    by_cases h : x.1=0 <;> simp [insert,value,h]
  | cons y ys ih =>
    rw [insert]
    split_ifs with hx hk hc
    · simp only [hx,Int.cast_zero,zero_mul,zero_add]
    · have he : (x.1 : R)+(y.1 : R)=0 := by rw [← Int.cast_add,hc,Int.cast_zero]
      rw [value_cons,← hk]
      linear_combination -(pair x.2)*he
    · simp only [value_cons,Int.cast_add]
      rw [← hk]
      ring
    · rw [value_cons,ih,value_cons]
      ring
lemma value_collect_aux (pair : Key → R) (a acc : TwoForm) :
    value pair (a.foldl (fun out x => insert x out) acc)=value pair a+value pair acc := by
  induction a generalizing acc with
  | nil => simp [value]
  | cons x xs ih =>
    rw [List.foldl_cons,ih,value_insert,value_cons]
    ring
lemma value_collect (pair : Key → R) (a : TwoForm) : value pair (collect a)=value pair a := by
  simpa [collect,value] using value_collect_aux pair a []
lemma value_zero (pair : Key → R) (a : TwoForm) (h : collect a = []) : value pair a=0 := by
  rw [← value_collect pair a,h]
  rfl
lemma universal_formal_pullbacks (pair : Key → R) :
    value pair (defect (wordKick 0))=0 ∧
    value pair (defect (wordKick 1))=0 ∧ value pair (defect wordDrift)=0 :=
  ⟨value_zero pair _ face0_normal,value_zero pair _ face1_normal,
    value_zero pair _ drift_normal⟩

def witnessPair (k : Key) : ℚ := if k=(0,7,[]) then 1 else 0
set_option maxHeartbeats 4000000 in
-- Evaluate one nonzero coefficient to exclude a zero baseline form.
lemma baseline_value : value witnessPair (twiceOmega original)=1 := by decide +kernel

/-! ## Non-vacuity -/
example : original.U 0=[(0,true)] ∧ original.P 6=[(13,true)] := ⟨rfl,rfl⟩
example : value (fun _ => (1 : ℚ)) (defect (wordKick 0))=0 :=
  (universal_formal_pullbacks _).1
example : value witnessPair (twiceOmega original) ≠ 0 := by rw [baseline_value]; norm_num
end Artform.Scores.NonabelianGravity.Maurer
