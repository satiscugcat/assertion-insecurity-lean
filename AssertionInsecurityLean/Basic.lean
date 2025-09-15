import Mathlib

inductive EX {A: Type} (P: A -> Type): Type
| intro (w: A) (h: P w)

inductive EQ {A: Type}: A -> A -> Type
| refl (r: A) : EQ r r

inductive TermVar
| cons : Nat -> TermVar
deriving DecidableEq

inductive KeyVar
| cons : Nat  -> KeyVar
deriving DecidableEq

inductive Name
| cons : Nat -> Name
deriving DecidableEq

inductive Var
| term (t: TermVar) 
| key (k:KeyVar)
deriving DecidableEq



inductive Key: Type
| priv (k: Name)
| pub (k: Name)
| var (v: KeyVar)
deriving DecidableEq

inductive Term: Type
| var (v: TermVar)
| name (m: Name)
| key (k: Key)
| pair (t1 t2: Term)
| enc (t: Term) (k: Key)
deriving DecidableEq

   
abbrev TermSet := Set Term

def var_to_term (v: Var) : Term :=
  match v with
  | Var.term v => Term.var v
  | Var.key v => Term.key (Key.var v)
 


def FVSetTerm : Term -> Set Var
| Term.var v => {Var.term v}
| Term.name _ => ∅ 
| Term.key (Key.var v) => {Var.key v}
| Term.key _ => ∅
| Term.pair t1 t2 =>  FVSetTerm t1 ∪ FVSetTerm t2
| Term.enc t' k => (FVSetTerm t') ∪
                           match k with 
                             | Key.var v => {Var.key v} 
                             | _ => ∅


      
inductive dy : TermSet -> Term -> Type
| ax {X: TermSet} {t: Term} (inH:  t ∈ X) : dy X t
| pk {X: TermSet} {k: Name} (kH: dy X (Term.key (Key.priv k)) ) : dy X (Term.key (Key.pub k))
                                                           
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dy X t1
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dy X t2
| pair {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dy X (Term.pair t1 t2)
                                                               
| sdec {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.priv k))) (kH: dy X (Term.key (Key.priv k))): dy X t
| senc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.priv k))) : dy X (Term.enc t (Key.priv k))
                                                                                     
| adec {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.pub k))) (kH: dy X (Term.key (Key.priv k))): dy X t
| aenc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.pub k))) : dy X (Term.enc t (Key.pub k))

inductive Assertion: Type
| eq (t u: Term)
| member (t₀: Term) (tlist: List Term)
| and (a₀ a₁ : Assertion)
| exist (a: Assertion) (x: Var)
| says (k: Name) (a: Assertion)
deriving DecidableEq



def FVSetAssertion (a: Assertion): Set Var :=
  match a with
  | Assertion.eq l r => FVSetTerm l ∪ FVSetTerm r
  | Assertion.member t tlist => FVSetTerm t ∪ List.foldr (fun t s => FVSetTerm t ∪ s) ∅ tlist
  | Assertion.and a₀ a₁ => FVSetAssertion a₀ ∪ FVSetAssertion a₁
  | Assertion.exist a x => FVSetAssertion a \ {x}
  | Assertion.says _ a => FVSetAssertion a

def FVSetTermSet (S: TermSet) : Set Var :=
  {x | ∃ t, t ∈ S ∧ x ∈ FVSetTerm t}

abbrev AssertionSet := Set Assertion

def FVSetAssertionSet (A: AssertionSet): Set Var :=
  {x | ∃ a, a ∈ A ∧ x ∈ FVSetAssertion a}


inductive TermSubTermPosition: Term → Term → List ℕ → Prop
| epsilon (t: Term): TermSubTermPosition t t []
| pair_left₀ {t t₁ t₂: Term} {pos: List ℕ} (proof: TermSubTermPosition t (Term.pair t₁ t₂) pos) : TermSubTermPosition t t₁ (0::pos)
| pair_right₁ {t t₁ t₂: Term} {pos: List ℕ} (proof: TermSubTermPosition t (Term.pair t₁ t₂) pos) : TermSubTermPosition t t₁ (0::pos)
| enc_term₀ (t t': Term) (k: Key) {pos: List ℕ} (proof: TermSubTermPosition t (Term.enc t' k) pos) : TermSubTermPosition t t' (0::pos)
| enc_name₁ (t t': Term) (k: Key) {pos: List ℕ} (proof: TermSubTermPosition t (Term.enc t' k) pos) : TermSubTermPosition t (Term.key k) (1::pos)

def TermPositionSet (t: Term) : Set (List ℕ):=
  {pos | ∃ t', TermSubTermPosition t t' pos}

inductive AssertionTermPosition: Assertion -> Term -> List ℕ -> Prop
| eq_left0 {t tsub: Term} {pos: List ℕ} (proof: TermSubTermPosition t tsub pos) (t': Term) : AssertionTermPosition (Assertion.eq t t') tsub (0::pos)
| eq_right₁ {t t' t'sub: Term} {pos: List ℕ} (t: Term)(proof: TermSubTermPosition t t'sub pos) : AssertionTermPosition (Assertion.eq t t') t'sub (1::pos)
| member_member₀  (t: Term) (tlist: List Term) : AssertionTermPosition (Assertion.member t tlist) t [0]
| member_disjunctionSi {i: Nat} {t: Term} {tlist: List Term} (t': Term) (proof: tlist[i]? = Option.some t): AssertionTermPosition (Assertion.member t' tlist) t' [(Nat.succ i)]
                                                                                                                                                        
| and_left₀ {a : Assertion} {tsub: Term} {pos: List Nat} (a' : Assertion) (proof: AssertionTermPosition a tsub pos) : AssertionTermPosition (Assertion.and a a') tsub (0::pos)
| and_right₁ {a': Assertion} {tsub: Term} {pos: List ℕ} (a: Assertion) (proof: AssertionTermPosition a' tsub pos) : AssertionTermPosition (Assertion.and a a') tsub (1::pos)

| exist_var₀ {a: Assertion} {pos: List Nat} {tsub: Term} {x: Var}  (proof: AssertionTermPosition a (var_to_term x) pos) : AssertionTermPosition (Assertion.exist a x) (var_to_term x) (0::pos)

| says_name₀₀ (k: Name) (a: Assertion): AssertionTermPosition (Assertion.says k a) (Term.name k) [0,0]
| says_key₀ (k: Name) (a: Assertion): AssertionTermPosition (Assertion.says k a) (Term.key (Key.pub k)) [0]
| says_ass₁ {a: Assertion} (k: Name) {tsub: Term} {pos: List ℕ} (proof: AssertionTermPosition a tsub pos): AssertionTermPosition (Assertion.says k a) tsub (1::pos)

def AssertionPositionSet (a: Assertion) : Set (List ℕ):=
  {pos | ∃ t', AssertionTermPosition a t' pos}

def AssertionTermPositionSet (a: Assertion) (t: Term) : Set (List ℕ) :=
  {pos | AssertionTermPosition a t pos}

inductive ProperPrefix: List ℕ -> List ℕ -> Prop
| hd (hd: Nat) {tl: List Nat} (nonempty: tl ≠ []) : ProperPrefix [hd] (hd::tl)
| cons {hd: Nat} {tl1 tl2: List Nat} (proof: ProperPrefix tl1 tl2) : ProperPrefix (hd::tl1) (hd::tl2)

def AssertionSubTerm (a: Assertion) (t: Term) := ∃ pos, AssertionTermPosition a t pos

def AssertionSubTermSet (a: Assertion) : TermSet := {t | AssertionSubTerm a t}
def AssertionSetSubTermSet (A: AssertionSet) : TermSet:= {t | ∃ a, a ∈ A ∧ AssertionSubTerm a t}



def AssertionMaximalSubTerm (a: Assertion) (t: Term) :=
 ∃ pos, (AssertionTermPosition a t pos ∧ (¬ (∃ t' pos', AssertionTermPosition a t' pos' ∧ ProperPrefix pos' pos)))

def QSet (pos: List ℕ) : Set (List ℕ) :=
{ pos' | pos' = [] ∨ ProperPrefix pos' pos }

inductive AbstractablePositionSetTerm : TermSet → Term → Set (List ℕ)
| cons {S: TermSet} {t: Term} {p: List ℕ} (positionTermProof: p ∈(TermPositionSet t))(abstractableProof: forall (q: List Nat) (t': Term), q ∈ (QSet p) -> TermSubTermPosition t t' q -> dy S t') : AbstractablePositionSetTerm S t p

inductive AbstractablePositionSetAssertion: TermSet -> Assertion -> Set (List ℕ)
| eq_left₀ {S: TermSet} {t₀: Term} {pos: List ℕ} (t₁: Term) (proof: AbstractablePositionSetTerm S t₀ pos) : AbstractablePositionSetAssertion S (Assertion.eq t₀ t₁) (0::pos)
| eq_right₁ {S: TermSet} {t₁: Term} {pos: List ℕ} (t₀: Term) (proof: AbstractablePositionSetTerm S t₁ pos): AbstractablePositionSetAssertion S (Assertion.eq t₀ t₀) (1::pos)
| member₀ (S: TermSet) {n: ℕ} (t₀: Term) (tList : List Term) : AbstractablePositionSetAssertion S (Assertion.member t₀ tList) [0]
| and_left₀ {S:TermSet} {a : Assertion} {pos: List ℕ} (proof: pos ∈ (AbstractablePositionSetAssertion S a)) (a' : Assertion): AbstractablePositionSetAssertion S (Assertion.and a a') (0::pos)
| and_right₁ {S: TermSet} {a': Assertion} {pos: List ℕ} (a: Assertion) (proof: pos ∈ AbstractablePositionSetAssertion S a'): AbstractablePositionSetAssertion S (Assertion.and a a') (1::pos)
| exists_var₀ {S: TermSet} {pos: List ℕ} (a: Assertion) {x: Var} (proof: pos ∈ AbstractablePositionSetAssertion ( S ∪ {var_to_term x}) a):
  AbstractablePositionSetAssertion S (Assertion.exist a x)
    (0::pos)
| says_pub₀ (S: TermSet) (k: Name) (a: Assertion) : AbstractablePositionSetAssertion S (Assertion.says k a) [0]
| says_ass₁ {S: TermSet} (k: Name) {a: Assertion} {pos: List ℕ} (proof: pos ∈ AbstractablePositionSetAssertion S a): AbstractablePositionSetAssertion S (Assertion.says k a) (1::pos)




@[simp]
def intersection {A: Type} [DecidableEq A]: List A -> List A -> List A
| [], _ => []
| hd::tl, l => if (hd ∈ l ∧ hd ∉ (intersection tl l)) 
                 then hd::(intersection tl l)
                 else intersection tl l

      
    
mutual                   
inductive eq_ady: TermSet -> AssertionSet -> Assertion -> Type
| ax (S: TermSet) {A: AssertionSet} {alpha: Assertion} (proof: alpha ∈ A): eq_ady S A alpha
| eq {S: TermSet} (A: AssertionSet) {t: Term} (proof: dy S t) : eq_ady S A (Assertion.eq t t)
                                                                     
| cons_pair {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p1: eq_ady S A (Assertion.eq t1 u1)) (p2: eq_ady S A (Assertion.eq t2 u2)): eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))

| cons_enc {S: TermSet} {A: AssertionSet} {t1 t2: Term} {k1 k2: Key} (p1: eq_ady S A (Assertion.eq t1 t2)) (p2: eq_ady S A (Assertion.eq ((Term.key k1)) (Term.key k2 ))): eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))

| cons_pk {S: TermSet} {A: AssertionSet} {k1 k2: Name} (p: eq_ady S A (Assertion.eq ((Term.key (Key.priv k1))) (Term.key (Key.priv k2) )) ): eq_ady S A (Assertion.eq ((Term.key (Key.pub k1))) (Term.key (Key.pub k2) ))

| sym {S: TermSet} {A: AssertionSet} {t u: Term} (p: eq_ady S A (Assertion.eq t u)) : eq_ady S A (Assertion.eq u t)
 
| trans {S: TermSet} {A: AssertionSet} {t1 tk: Term} (p: Eq_Trans S A t1 tk): eq_ady S A (Assertion.eq t1 tk)

| proj_pair_left {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) (pin: {[0,0], [0, 1], [1, 0], [1, 1]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) ) : eq_ady S A (Assertion.eq t1 u1)
| proj_pair_right {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2)))  (pin: {[0,0], [0, 1], [1, 0], [1, 1]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) ) : eq_ady S A (Assertion.eq t2 u2)
                                   
          
| proj_enc_term {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) (pin: {[0,0], [0, 1], [1, 0], [1, 1]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) ): eq_ady S A (Assertion.eq t1 t2)
| proj_enc_key {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) (pin: {[0,0], [0, 1], [1, 0], [1, 1]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) ): eq_ady S A (Assertion.eq (Term.key k1) (Term.key k2))

| proj_pk {S: TermSet} {A: AssertionSet} {k1 k2: Name} (p: eq_ady S A (Assertion.eq ((Term.key (Key.pub k1))) (Term.key (Key.pub k2)))) (pin: {[0,0], [1,0]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq ((Term.key (Key.pub k1))) (Term.key (Key.pub k2))) )): eq_ady S A (Assertion.eq ((Term.key (Key.priv k1))) (Term.key (Key.priv k2) ))

| subst {S: TermSet} {A: AssertionSet} {t u: Term} {l: List Term} (proofMember: eq_ady S A (Assertion.member t l)) (proofEq: eq_ady S A (Assertion.eq t u)): eq_ady S A (Assertion.member u l)

| prom {S: TermSet} {A: AssertionSet} {t n: Term} (proof: eq_ady S A (Assertion.member t [n])) : eq_ady S A (Assertion.eq t n)

| int {S: TermSet} {A: AssertionSet} {t: Term} {l: List Term} (premises: Eq_Int S A t l): eq_ady S A (Assertion.member t l)
| wk {S: TermSet} {A: AssertionSet} {t n: Term} {nlist: List Term} (proofEq: eq_ady S A (Assertion.eq t n)) (proofIn: n ∈ nlist) (proofValid: Eq_Wk S nlist): eq_ady S A (Assertion.member t nlist)

inductive Eq_Trans: TermSet -> AssertionSet -> Term -> Term -> Type
| two_trans {S: TermSet} {A: AssertionSet} {t1 t2 t3: Term} (p1: eq_ady S A (Assertion.eq t1 t2)) (p2: eq_ady S A (Assertion.eq t2 t3)): Eq_Trans S A t1 t3
| trans_trans {S: TermSet} {A: AssertionSet} {t1 tk tk': Term} (phead: eq_ady S A (Assertion.eq t1 tk)) (plist: Eq_Trans S A tk tk'): Eq_Trans S A t1 tk'                                                           
inductive Eq_Int: TermSet -> AssertionSet -> Term -> List Term -> Type
| two_lists {S: TermSet} {A: AssertionSet} {t: Term} {l1 l2: List Term}  (proof1: eq_ady S A (Assertion.member t l1)) (proof2: eq_ady S A (Assertion.member t l2)): Eq_Int S A t (intersection l1 l2)
| new_list {S: TermSet} {A: AssertionSet} {t: Term} {l l': List Term} (proof1: eq_ady S A (Assertion.member t l)) (proof2: Eq_Int S A t l'): Eq_Int S A t (intersection l l')
                                                                                                                                                                                                                                                                             
inductive Eq_Wk: TermSet -> List Term -> Type
| single {S: TermSet} {t: Term} (proof: dy S t): Eq_Wk S [t]
| new {S: TermSet} {t: Term} {tlist: List Term} (proofNew: dy S t) (proofList: Eq_Wk S tlist): Eq_Wk S (t::tlist)
end

def pkRecursor {S A t u}  (p: Eq_Trans S A t u) : 
        Option (
          (EX fun (tk: Name)  => EX fun (xk: Name) =>
              eq_ady S A (Assertion.eq  (Term.key (Key.priv tk)) (Term.key (Key.priv xk))) × (eq_ady S A (Assertion.eq (Term.key (Key.pub xk)) u)) × (EQ t (Term.key (Key.pub tk)))) ⊕  
          (EX fun (uk: Name) => EX fun (xk: Name) => 
              eq_ady S A (Assertion.eq t ((Term.key (Key.pub xk)))) × eq_ady S A (Assertion.eq (Term.key (Key.priv xk)) (Term.key (Key.priv uk))) ×  EQ u  (Term.key (Key.pub uk))) ⊕ 
          (EX fun (xk: Name) => EX fun (yk: Name) =>
              eq_ady S A (Assertion.eq t (Term.key (Key.pub xk))) × eq_ady S A (Assertion.eq (Term.key (Key.priv xk)) (Term.key (Key.priv yk))) × eq_ady S A (Assertion.eq (Term.key (Key.pub yk)) u)) ⊕ 
          (EX fun (tk: Name) =>  EX fun (xk: Name) =>
              eq_ady S A (Assertion.eq (Term.key (Key.priv tk)) (Term.key (Key.priv xk))) ×  Eq_Trans S A (Term.key (Key.pub xk)) u ×  EQ t ((Term.key (Key.pub tk)))) ⊕  
          (EX fun (uk: Name) => EX fun (xk: Name) => 
              Eq_Trans S A t (Term.key (Key.pub xk)) × eq_ady S A (Assertion.eq (Term.key (Key.priv xk)) (Term.key (Key.priv uk))) ×  EQ u (Term.key (Key.pub uk))) ⊕ 
          (EX fun (xk: Name) => EX fun (yk: Name) =>
              Eq_Trans S A t (Term.key (Key.pub xk)) × eq_ady S A (Assertion.eq (Term.key (Key.priv xk)) (Term.key (Key.priv yk))) × eq_ady S A (Assertion.eq (Term.key (Key.pub yk)) u)) ⊕ 
          (EX fun (xk: Name) => EX fun (yk: Name) =>
              eq_ady S A (Assertion.eq t (Term.key (Key.pub xk))) × eq_ady S A (Assertion.eq (Term.key (Key.priv xk)) (Term.key (Key.priv yk))) ×  Eq_Trans S A (Term.key (Key.pub yk)) u) ⊕
          (EX fun (xk: Name) => EX fun (yk: Name) =>
              Eq_Trans S A t (Term.key (Key.pub xk)) × eq_ady S A (Assertion.eq (Term.key (Key.priv xk)) (Term.key (Key.priv yk))) ×  Eq_Trans S A (Term.key (Key.pub yk)) u))
         := 
    by
      cases p with
      | two_trans p1 p2 =>
        match p1 with
        | @eq_ady.cons_pk _ _ tk xk p => 
          apply Option.some
          apply Sum.inl
          apply EX.intro tk
          apply EX.intro xk
          apply (p, p2, by apply EQ.refl)
        | p1 => 
         match p2 with
        | @eq_ady.cons_pk _ _ xk uk p => 
          apply Option.some
          apply Sum.inr; apply Sum.inl
          apply EX.intro uk
          apply EX.intro xk
          apply (p1, p, by apply EQ.refl)
        | p2 => apply Option.none
      | trans_trans phead ptail => 
        match phead with
        | @eq_ady.cons_pk _ _ tk xk p =>
          apply Option.some
          apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inl
          apply EX.intro tk
          apply EX.intro xk
          apply (p, ptail, by apply EQ.refl)
        | phead =>
          match (pkRecursor ptail) with
          | Option.none => apply Option.none
          
          | Option.some (Sum.inl p) =>
            rcases p with ⟨tk, xk, p1, p2, _, _⟩
            apply Option.some; apply Sum.inr; apply Sum.inr; apply Sum.inl
            apply EX.intro tk
            apply EX.intro xk
            apply (phead, p1, p2)
            
                  
          | Option.some (Sum.inr (Sum.inl p)) => 
            rcases p with ⟨uk, xk, p1, p2, _, _⟩
            apply Option.some; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inl
            apply EX.intro uk; apply EX.intro xk
            apply (Eq_Trans.two_trans phead p1, p2, by apply EQ.refl)
            
          
          | Option.some (Sum.inr (Sum.inr (Sum.inl p))) => 
            rcases p with ⟨xk, yk, p1, p2, p3⟩
            apply Option.some; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inl
            apply EX.intro xk; apply EX.intro yk
            apply (Eq_Trans.two_trans phead p1, p2, p3)
           
         
          | Option.some (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) =>
            rcases p with ⟨tk, xk, p1, p2, _, _⟩
            apply Option.some; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inl
            apply EX.intro tk; apply EX.intro xk
            apply (phead, p1, p2)
            
          | Option.some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) =>
            rcases p with ⟨uk, xk, p1, p2, _, _⟩
            apply Option.some; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inl
            apply EX.intro uk; apply EX.intro xk
            apply (Eq_Trans.trans_trans phead p1, p2, by apply EQ.refl)
            
          | Option.some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))) =>
            rcases p with ⟨xk, yk, p1, p2, p3⟩
            apply Option.some; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inl
            apply EX.intro xk; apply EX.intro yk
            apply (Eq_Trans.trans_trans phead p1, p2, p3)
            
                  
          | Option.some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))))) => 
            rcases p with ⟨xk, yk, p1, p2, p3⟩
            apply Option.some; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr
            apply EX.intro xk; apply EX.intro yk
            apply (Eq_Trans.two_trans phead p1, p2, p3)
            
          
          | Option.some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))))) => 
            rcases p with ⟨xk, yk, p1, p2, p3⟩
            apply Option.some; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inr
            apply EX.intro xk; apply EX.intro yk
            apply (Eq_Trans.trans_trans phead p1, p2, p3)
